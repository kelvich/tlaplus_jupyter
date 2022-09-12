# coding: utf-8

import argparse
import json
import os
import sys
import shutil
import binascii

from future.standard_library import install_aliases
install_aliases()
from urllib.request import urlretrieve

from jupyter_client.kernelspec import KernelSpecManager
from IPython.utils.tempdir import TemporaryDirectory

TOOLS_URI = "https://github.com/tlaplus/tlaplus/releases/download/v1.7.2/tla2tools.jar"

kernel_json = {
    "argv": [sys.executable, "-m", "tlaplus_jupyter", "-f", "{connection_file}"],
    "display_name": "TLA⁺",
    "language": "tla",
    "codemirror_mode": "tlaplus"
}

def install_my_kernel_spec(user=True, prefix=None):
    with TemporaryDirectory() as td:
        os.chmod(td, 0o755) # Starts off as 700, not user readable
        with open(os.path.join(td, 'kernel.json'), 'w') as f:
            json.dump(kernel_json, f, sort_keys=True)

        # copy kernel.js
        js_path = os.path.join(os.path.dirname(__file__), 'assets', 'kernel.js')
        shutil.copy(js_path, td)

        print('Installing Jupyter kernel spec')
        KernelSpecManager().install_kernel_spec(td, 'tlaplus_jupyter', user=user, prefix=prefix)

def _is_root():
    try:
        return os.geteuid() == 0
    except AttributeError:
        return False # assume not an admin on non-Unix platforms

def main(argv=None):
    ap = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument('--user', action='store_true',
        help="Install to the per-user kernels registry. Default if not root.")
    ap.add_argument('--sys-prefix', action='store_true',
        help="Install to sys.prefix (e.g. a virtualenv or conda env)")
    ap.add_argument('--prefix',
        help="Install to the given prefix. "
             "Kernelspec will be installed in\n"
             "{PREFIX}/share/jupyter/kernels/")
    ap.add_argument('--tlc-exec-stats', choices=['share', 'no-id', 'disable'],
        default="share",
        help="Share execution statistics to guide TLC development.\n"
             " share -- always share execution statistics\n"
             " no-id -- share without installation identifier\n"
             " disable -- never share\n"
             "Default is to share. Re-installation with a new value will override\n"
             "previous decision. Details of data collected can be found at\n"
             "https://github.com/tlaplus/tlaplus/blob/master/tlatools/src/util/ExecutionStatisticsCollector.md"
        )
    args = ap.parse_args(argv)

    if args.sys_prefix:
        args.prefix = sys.prefix
    if not args.prefix and not _is_root():
        args.user = True

    install_my_kernel_spec(user=args.user, prefix=args.prefix)

    # install tla2tools.jar
    vendor_dir = os.path.join(os.path.dirname(__file__), 'vendor')
    if not os.path.isdir(vendor_dir):
        os.mkdir(vendor_dir)
    jar_path = os.path.join(vendor_dir, 'tla2tools.jar')
    print("Downloading tla2tools.jar to " + jar_path)
    urlretrieve(TOOLS_URI, jar_path)

    # install stats collector id
    tla_dir = os.path.join(os.path.expanduser("~"), ".tlaplus")
    if not os.path.isdir(tla_dir):
        os.mkdir(tla_dir)
    statfile_path = os.path.join(tla_dir, "esc.txt")

    old_content = None
    if os.path.isfile(statfile_path):
        with open(statfile_path, "r") as f:
            old_content = f.read().strip()

    with open(statfile_path, "w") as f:
        if args.tlc_exec_stats == "share":
            # do not rewrite id if it is already present
            if old_content == None or len(old_content) != 32:
                token = binascii.b2a_hex(os.urandom(16)).decode()
                f.write(token)
            else:
                f.write(old_content)
        elif args.tlc_exec_stats == "no-id":
            f.write("RANDOM_IDENTIFIER")
        else:
            f.write("NO_STATISTICS")
        f.write("\n")

if __name__ == '__main__':
    main()
