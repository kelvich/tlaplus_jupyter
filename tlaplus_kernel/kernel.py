import os
import tempfile
import sys
import re
import logging
import shutil

from ipykernel.kernelbase import Kernel
from subprocess import Popen, PIPE, STDOUT

# logging.basicConfig(filename='tlaplus_kernel.log', level=logging.DEBUG)

class TLAPlusKernel(Kernel):
    implementation = 'tlaplus_kernel'
    implementation_version = '0.1'
    language = 'TLA+'
    language_version = '2.13'
    language_info = {
        'name': 'tlaplus',
        'mimetype': 'text/x-tlaplus',
        'file_extension': '.tla',
        'codemirror_mode': 'tlaplus'
    }
    banner = "TLA+"

    def __init__(self, *args, **kwargs):
        super(TLAPlusKernel, self).__init__(*args, **kwargs)
        self.modules = {}
        self.mod_re = re.compile("^\s*-----*\s*MODULE\s+(\w+)\s")
        self.tlc_re = re.compile("^\s*!tlc:([^\s]+)\s+")
        self.vendor_path = os.path.join(os.path.dirname(__file__), 'vendor')

    def dispatch_code(self, code):
        # module
        if self.mod_re.match(code):
            logging.info("got module '%s'", code)
            module_name = self.mod_re.match(code).group(1)
            self.modules[module_name] = code
            res = self.run_model(module_name, tlc=False)
            if 'Fatal' not in res:
                res = ''
        # run config
        elif self.tlc_re.match(code):
            logging.info("got run config '%s'", code)
            module_name = self.tlc_re.match(code).group(1)
            if module_name in self.modules:
                config = self.tlc_re.sub('',code)
                res = self.run_model(module_name, tlc=True, cfg=config)
            else:
                res = "Module '{}' not found.\n".format(module_name)
                res += "Module should be defined and evaluated in some cell before tlc run."
        # constant expression
        else:
            logging.info("got expression '%s'", code)
            res = self.run_expr(code)
        return res

    def run_model(self, name, tlc=True, cfg=''):
        workspace = tempfile.mkdtemp()

        assert(name in self.modules)
        # dump defined modules
        for module in self.modules:
            f = open(os.path.join(workspace, module + '.tla'), 'w')
            f.write(self.modules[module])
            f.close()

        # dump config
        if tlc:
            f = open(os.path.join(workspace, 'run.cfg'), 'w')
            f.write(cfg)
            f.close()

        cmd = ['java', '-cp', os.path.join(self.vendor_path, 'tla2tools.jar')]
        if tlc:
            cmd += ['tlc2.TLC', '-deadlock']
            cmd += ['-config', 'run.cfg']
        else:
            cmd += ['tla2sany.SANY']
        cmd += [name + '.tla']

        logging.info("run_model '%s'", cmd)
        proc = Popen(cmd, stdout=PIPE, stdin=PIPE, stderr=PIPE, cwd=workspace)
        out = proc.communicate()[0].decode()
        logging.info("run_model got response '%s'", out)

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
        raw = self.run_model('expr')
        raw_lines = raw.split("\n")

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
        if not silent:
            stream_content = {'name': 'stdout', 'text': self.dispatch_code(code)}
            self.send_response(self.iopub_socket, 'stream', stream_content)

        return {'status': 'ok',
                # The base class increments the execution count
                'execution_count': self.execution_count,
                'payload': [],
                'user_expressions': {},
               }
