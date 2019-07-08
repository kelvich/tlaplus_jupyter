import os, tempfile
import sys
from ipykernel.kernelbase import Kernel
from subprocess import Popen, PIPE, STDOUT

class TLARunner():

    def run_model(self, source):
        vendor = os.path.join(os.path.dirname(__file__), 'vendor')

        workspace = tempfile.TemporaryDirectory()
        source = "---- MODULE expr ----\n" + source + "====\n"

        model = open(os.path.join(workspace.name, 'expr.tla'), 'w')
        model.write(source)
        model.flush()

        cmd = ['java', '-cp', os.path.join(vendor, "tla2tools.jar")]
        cmd += ['tlc2.TLC', '-deadlock']
        cmd += ['-config', os.path.join(vendor, "MC.cfg")]
        cmd += ['expr.tla']

        proc = Popen(cmd, stdout=PIPE, stdin=PIPE, stderr=PIPE, cwd=workspace.name)
        out = proc.communicate()[0].decode()

        model.close()
        workspace.cleanup()
        return out

    def run_expr(self, expr):

        # Wrap output in EXPR_BEGIN/EXPR_END to catch it later.
        # That method is due to github.com/will62794 and looks much nicer then
        # a regex-based set matching used in tla toolbox itself.
        model_src = """
        EXTENDS Naturals, Reals, Sequences, Bags, FiniteSets, TLC
        ASSUME PrintT("EXPR_BEGIN") /\ PrintT(%s) /\ PrintT("EXPR_END")
        """ % (expr)
        raw = self.run_model(model_src)
        raw_lines = raw.split("\n")

        if '"EXPR_BEGIN"' in raw_lines:
            start = raw_lines.index('"EXPR_BEGIN"')
            stop = raw_lines.index('"EXPR_END"')
            res = "\n".join(raw_lines[start+1:stop])
        else:
            # otherwise show full out with error
            res = raw
        return res


class TLAPlusKernel(Kernel):
    implementation = 'tlaplus_kernel'
    implementation_version = '0.1'
    language = 'TLA+'
    language_version = '1.5.7'
    language_info = {
        'name': 'TLA+',
        'mimetype': 'text/tlaplus',
        'file_extension': '.tla',
    }
    banner = "TLA+"

    def do_execute(self, code, silent, store_history=True, user_expressions=None,
                   allow_stdin=False):
        if not silent:
            tr = TLARunner()
            response = tr.run_expr(code)
            stream_content = {'name': 'stdout', 'text': response}
            self.send_response(self.iopub_socket, 'stream', stream_content)

        return {'status': 'ok',
                # The base class increments the execution count
                'execution_count': self.execution_count,
                'payload': [],
                'user_expressions': {},
               }
