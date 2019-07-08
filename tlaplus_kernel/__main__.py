from ipykernel.kernelapp import IPKernelApp
from . import TLAPlusKernel

IPKernelApp.launch_instance(kernel_class=TLAPlusKernel)
