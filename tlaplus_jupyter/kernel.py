import os
import tempfile
import sys
import re
import logging
import shutil

from ipykernel.kernelbase import Kernel
from subprocess import Popen, PIPE, STDOUT

# logging.basicConfig(filename='tlaplus_jupyter.log', level=logging.DEBUG)

class TLAPlusKernel(Kernel):
    implementation = 'tlaplus_jupyter'
    implementation_version = '0.1'
    language = 'TLA⁺'
    language_version = '2.13'
    language_info = {
        'name': 'tlaplus',
        'mimetype': 'text/x-tlaplus',
        'file_extension': '.tla',
        'codemirror_mode': 'tlaplus'
    }
    banner = "TLA⁺"

    def __init__(self, *args, **kwargs):
        super(TLAPlusKernel, self).__init__(*args, **kwargs)
        self.modules = {}
        self.mod_re = re.compile(r'^\s*-----*\s*MODULE\s+(\w+)\s')
        self.tlc_re = re.compile(r'^\s*!tlc:([^\s]+)\s+')
        self.vendor_path = os.path.join(os.path.dirname(__file__), 'vendor')

    def get_workspace(self):
        workspace = tempfile.mkdtemp()
        # dump defined modules
        for module in self.modules:
            f = open(os.path.join(workspace, module + '.tla'), 'w')
            f.write(self.modules[module])
            f.close()
        return workspace

    def tlatools_command(self):
        return [
            'java',
            '-cp', os.path.join(self.vendor_path, 'tla2tools.jar')
        ]

    def run_proc(self, cmd, workspace):
        logging.info("run_proc '%s'", cmd)

        proc = Popen(cmd, stdout=PIPE, stderr=PIPE, cwd=workspace)
        out, err = [s.decode() for s in proc.communicate()]

        logging.info("run_proc got response (rc=%d) stdout='%s' stderr='%s'",proc.returncode,out,err)

        if proc.returncode != 0 and out == "":
            out = "Failed to run tla2tools: %s" % (err)

        return out

    def eval_module(self, module_name, module_src):
        self.modules[module_name] = module_src
        workspace = self.get_workspace()
        new_src = None

        cmd = self.tlatools_command()
        cmd += ['tla2sany.SANY']
        cmd += [module_name + '.tla']

        out = self.run_proc(cmd, workspace)

        if 'Fatal' in out:
            shutil.rmtree(workspace)
            return (out, None)

        # run pcal.trans if needed
        if '--algorithm' in module_src or '--fair' in module_src:
            cmd = self.tlatools_command()
            cmd += ['pcal.trans']
            cmd += [module_name + '.tla']

            out = self.run_proc(cmd, workspace)

            if 'error' in out:
                shutil.rmtree(workspace)
                return (out, None)

            with open(os.path.join(workspace, module_name + '.tla')) as f:
                new_src = f.read()

            self.modules[module_name] = new_src
            logging.info("eval_module update module src '%s'", new_src)

        shutil.rmtree(workspace)
        return ('', new_src)

    def run_tlc(self, module_name, cfg=''):
        assert(module_name in self.modules)

        workspace = self.get_workspace()

        # dump config
        f = open(os.path.join(workspace, 'run.cfg'), 'w')
        f.write(cfg)
        f.close()

        cmd = self.tlatools_command()
        cmd += ['tlc2.TLC', '-deadlock']
        cmd += ['-config', 'run.cfg']
        cmd += [module_name + '.tla']

        out = self.run_proc(cmd, workspace)

        shutil.rmtree(workspace)
        return out

    def run_expr(self, expr):
        # Wrap output in EXPR_BEGIN/EXPR_END to catch it later.
        # That method is due to github.com/will62794 and looks much nicer then
        # a regex-based set matching used in tla toolbox itself.
        model_src = """
        ---- MODULE expr ----
        EXTENDS Naturals, Reals, Sequences, Bags, FiniteSets, TLC
        ASSUME PrintT("EXPR_BEGIN") /\ PrintT(%s) /\ PrintT("EXPR_END")
        ====
        """ % (expr)
        self.modules['expr'] = model_src
        raw = self.run_tlc('expr')
        raw_lines = raw.splitlines()

        if '"EXPR_BEGIN"' in raw_lines and '"EXPR_END"' in raw_lines:
            start = raw_lines.index('"EXPR_BEGIN"')
            stop = raw_lines.index('"EXPR_END"')
            res = "\n".join(raw_lines[start+1:stop])
        else:
            # otherwise show full out with error
            res = raw
        return res

    def do_execute(self, code, silent, store_history=True, user_expressions=None,
                   allow_stdin=False):

        # expression result
        res = ''
        # new cell content if needed
        code_update = None

        # module
        if self.mod_re.match(code):
            logging.info("got module '%s'", code)
            module_name = self.mod_re.match(code).group(1)
            res, code_update = self.eval_module(module_name, code)
        # run config
        elif self.tlc_re.match(code):
            logging.info("got run config '%s'", code)
            module_name = self.tlc_re.match(code).group(1)
            if module_name in self.modules:
                config = self.tlc_re.sub('',code)
                res = self.run_tlc(module_name, cfg=config)
            else:
                res = "Module '{}' not found.\n".format(module_name)
                res += "Module should be defined and evaluated in some cell before tlc run."
        # constant expression
        else:
            logging.info("got expression '%s'", code)
            res = self.run_expr(code)

        self.send_response(self.iopub_socket, 'stream', {
            'name': 'stdout',
            'text': res
        })

        return {
            'status': 'ok',
            # The base class increments the execution count
            'execution_count': self.execution_count,
            'payload': [
                {
                    "source": "set_next_input",
                    "text": code_update,
                    "replace": True,
                } if code_update else {}
            ],
            'user_expressions': {},
        }
