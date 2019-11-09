# coding: utf-8

import argparse
import json
import os
import sys
import shutil

from future.standard_library import install_aliases
install_aliases()
from urllib.request import urlretrieve

from jupyter_client.kernelspec import KernelSpecManager
from IPython.utils.tempdir import TemporaryDirectory

TOOLS_URI = "https://github.com/tlaplus/tlaplus/releases/download/v1.6.0/tla2tools.jar"

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
    ap = argparse.ArgumentParser()
    ap.add_argument('--user', action='store_true',
        help="Install to the per-user kernels registry. Default if not root.")
    ap.add_argument('--sys-prefix', action='store_true',
        help="Install to sys.prefix (e.g. a virtualenv or conda env)")
    ap.add_argument('--prefix',
        help="Install to the given prefix. "
             "Kernelspec will be installed in {PREFIX}/share/jupyter/kernels/")
    args = ap.parse_args(argv)

    if args.sys_prefix:
        args.prefix = sys.prefix
    if not args.prefix and not _is_root():
        args.user = True

    install_my_kernel_spec(user=args.user, prefix=args.prefix)

    vendor_dir = os.path.join(os.path.dirname(__file__), 'vendor')
    try:
        os.mkdir(vendor_dir)
    except FileExistsError:
        pass
    jar_path = os.path.join(vendor_dir, 'tla2tools.jar')
    print("Downloading tla2tools.jar to " + jar_path)
    urlretrieve(TOOLS_URI, jar_path)

if __name__ == '__main__':
    main()
