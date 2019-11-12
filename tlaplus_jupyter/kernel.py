# coding: utf-8

import os
import tempfile
import re
import logging
import shutil
import psutil
import subprocess
import traceback

from ipykernel.kernelbase import Kernel


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
        self.vendor_path = os.path.join(os.path.dirname(__file__), 'vendor')
        self.logfile = None

    def get_workspace(self):
        workspace = tempfile.mkdtemp()
        # dump defined modules
        for module in self.modules:
            f = open(os.path.join(workspace, module + '.tla'), 'w')
            f.write(self.modules[module])
            f.close()
        return workspace

    def java_command(self):
        return [
            'java',
            '-XX:+UseParallelGC',
            '-cp', os.path.join(self.vendor_path, 'tla2tools.jar')
        ]

    def run_proc(self, cmd, workspace):
        logging.info("run_proc started '%s'", cmd)

        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=workspace)
        out, _ = proc.communicate()
        out = out.decode()

        logging.info(out)
        logging.info("run_proc finished (rc=%d)", proc.returncode)

        return (out, proc.returncode)

    def respond(self, res):
        self.send_response(self.iopub_socket, 'stream', {
            'name': 'stdout',
            'text': res
        })

        return {
            'status': 'ok',
            'execution_count': self.execution_count,
            'user_expressions': {},
        }

    def respond_with_error(self, err):
        self.send_response(self.iopub_socket, 'stream', {
            'name': 'stderr',
            'text': err
        })
        return {
            'status': 'error',
            'execution_count': self.execution_count,
            'user_expressions': {},
        }

    def do_execute(self, payload, silent, store_history=True, user_expressions=None,
                   allow_stdin=False):
        """Route execute request depending on type."""

        try:
            # module
            if re.match(r'^\s*-----*\s*MODULE\s', payload):
                return self.eval_module(payload)

            # run config
            elif re.match(r'^\s*%tlc:', payload):
                return self.eval_tlc_config(payload)

            # tollge log collection
            elif re.match(r'^\s*%log', payload):
                return self.toggle_log(payload)

            # otherwise treat payload as a constant expression
            else:
                return self.eval_expr(payload)

        except Exception:
            return self.respond_with_error(traceback.format_exc())

    def eval_module(self, module_src):

        logging.info("eval_module '%s'", module_src)

        match = re.match(r'^\s*-----*\s*MODULE\s+(\w+)\s', module_src)
        if not match:
            return self.respond_with_error("Can't parse module name, please check module header.")

        module_name = match.group(1)
        self.modules[module_name] = module_src

        workspace = self.get_workspace()
        new_src = None

        cmd = self.java_command()
        cmd += ['tla2sany.SANY']
        cmd += [module_name + '.tla']

        out, rc = self.run_proc(cmd, workspace)

        if rc != 0:
            shutil.rmtree(workspace)
            return self.respond_with_error(out)

        # run pcal.trans if needed
        if '--algorithm' in module_src or '--fair' in module_src:
            cmd = self.java_command()
            cmd += ['pcal.trans']
            cmd += [module_name + '.tla']

            out, rc = self.run_proc(cmd, workspace)
            if rc != 0:
                shutil.rmtree(workspace)
                return self.respond_with_error(out)

            # read rewritten tla file with translation
            with open(os.path.join(workspace, module_name + '.tla')) as f:
                new_src = f.read()

            self.modules[module_name] = new_src
            logging.info("eval_module update module src '%s'", new_src)

        shutil.rmtree(workspace)
        return {
            'status': 'ok',
            'execution_count': self.execution_count,
            'payload': [
                {
                    "source": "set_next_input",
                    "text": new_src,
                    "replace": True,
                } if new_src else {}
            ],
            'user_expressions': {},
        }

    def eval_tlc_config(self, cfg):
        logging.info("eval_tlc_config '%s'", cfg)

        tlc_re = r'^\s*%tlc:([^\s]*)(.*)'
        match = re.match(tlc_re, cfg)
        module_name = match.group(1)
        extra_params = match.group(2).strip()
        extra_params = [] if extra_params == '' else extra_params.split()

        # bail out if module is not found
        if module_name not in self.modules:
            err = "Module '{}' not found.\n".format(module_name)
            err += "Module should be defined and evaluated in some cell before TLC run."
            return self.respond_with_error(err)

        # XXX: move to with and fill
        workspace = self.get_workspace()

        # dump config
        # XXX: with
        cfg = re.sub(tlc_re, '', cfg)
        f = open(os.path.join(workspace, 'run.cfg'), 'w')
        f.write(cfg)
        f.close()

        cmd = self.java_command()
        cmd += ['tlc2.TLC']
        cmd += ['-workers', str(psutil.cpu_count())]
        cmd += ['-config', 'run.cfg']
        cmd += extra_params
        cmd += [module_name + '.tla']

        # run TLC and redirect stderr to stdout
        logging.info("running '%s'", cmd)
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=workspace)
        with proc.stdout:
            for line in iter(proc.stdout.readline, b''):
                self.send_response(self.iopub_socket, 'stream', {
                    'name': 'stdout',
                    'text': line.decode()
                })
                logging.info("> ", line.decode())

        # wait for proc to exit and set returncode
        proc.wait()
        logging.info("tlc finished with rc=%d", proc.returncode)

        shutil.rmtree(workspace)

        # make sence to show all command if some TLC keywords were set
        if extra_params and proc.returncode != 0:
            self.send_response(self.iopub_socket, 'stream', {
                'name': 'stderr',
                'text': "Failed command was: '%s'" % ' '.join(cmd)
            })

        return {
            'status': 'ok' if proc.returncode == 0 else 'error',
            'execution_count': self.execution_count,
            'user_expressions': {},
        }


    def eval_expr(self, expr):

        logging.info("got expression '%s'", expr)

        # Wrap output in EXPR_BEGIN/EXPR_END to catch it later.
        # That method is due to github.com/will62794 and looks much nicer then
        # a regex-based set matching used in tla toolbox itself.
        model_src = """---- MODULE expr ----
EXTENDS Naturals, Reals, Sequences, Bags, FiniteSets, TLC
ASSUME PrintT("EXPR_BEGIN") /\ PrintT(
%s
) /\ PrintT("EXPR_END")
====\n""" % (expr)
        self.modules['expr'] = model_src

        logging.info("eval_expr final source '%s'", model_src)

        workspace = self.get_workspace()

        # dump config
        f = open(os.path.join(workspace, 'run.cfg'), 'w')
        f.write('')
        f.close()

        cmd = self.java_command()
        cmd += ['tlc2.TLC']
        cmd += ['-config', 'run.cfg']
        cmd += ['expr.tla']

        out, rc = self.run_proc(cmd, workspace)

        shutil.rmtree(workspace)

        raw_lines = out.splitlines()

        if rc != 0 or not ('"EXPR_BEGIN"' in raw_lines and '"EXPR_END"' in raw_lines):
            return self.respond_with_error(model_src + "\n" + out)

        start = raw_lines.index('"EXPR_BEGIN"')
        stop = raw_lines.index('"EXPR_END"')
        res = "\n".join(raw_lines[start+1:stop])

        return self.respond(res)


    def toggle_log(self, payload):
        """Runtime accessible logger"""

        cmd = re.match(r'^\s*%log\s*([^\s]*)', payload).group(1)

        if cmd == "on":
            if not self.logfile:
                self.logfile = tempfile.NamedTemporaryFile(delete=False)

                handler = logging.FileHandler(self.logfile.name, 'a')
                logger = logging.getLogger()
                logger.setLevel(logging.DEBUG)
                logger.addHandler(handler)

                return self.respond("Logging enabled")
            else:
                return self.respond("Logging already enabled")

        elif cmd == "off":
            logger = logging.getLogger()
            logger.setLevel(logging.ERROR)
            for handle in logger.handlers:
                logger.removeHandler(handle)
            if self.logfile:
                self.logfile.close()
                os.unlink(self.logfile.name)
                self.logfile = None

            return self.respond("Logging disabled")

        elif cmd == "":
            if self.logfile:
                with open(self.logfile.name, 'r') as file:
                    data = file.read()
                return self.respond(data)
            else:
                return self.respond_with_error("You need to enable logging first by evaluating '%log on'")

        else:
            return self.respond_with_error("Unknown log command. Valid command are '%log'/'%log on'/'%log off'")
