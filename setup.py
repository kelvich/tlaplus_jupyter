from setuptools import setup

with open('README.md') as f:
    readme = f.read()

setup(
    name='tlaplus_kernel',
    version='0.1',
    packages=['tlaplus_kernel'],
    description='Jupyter kernel for TLA+',
    author='Stas Kelvich',
    author_email='stas.kelvich@gmail.com',
    url='https://github.com/kelvich/tlaplus_kernel',
    long_description=readme,
    long_description_content_type="text/markdown",
    include_package_data=True,
    test_suite='tests',
    install_requires=[
        'jupyter_client', 'IPython', 'ipykernel', 'future'
    ],
    zip_safe=False
)
