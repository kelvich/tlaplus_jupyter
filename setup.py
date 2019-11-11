# coding: utf-8

from setuptools import setup

with open('README.md') as f:
    readme = f.read()

setup(
    name='tlaplus_jupyter',
    version='0.1',
    packages=['tlaplus_jupyter'],
    description='Jupyter kernel for TLA⁺',
    author='Stas Kelvich',
    author_email='stas.kelvich@gmail.com',
    url='https://github.com/kelvich/tlaplus_jupyter',
    long_description=readme,
    long_description_content_type="text/markdown",
    include_package_data=True,
    test_suite='tests',
    install_requires=[
        # notebook is not actually needed, but it's simpler to install
        'notebook>=5.7.8',
        'jupyter-client>=5.3.4',
        'ipykernel>=4.10.1',
        'future>=0.18',
        'psutil>=5.6.5'
    ],
    zip_safe=False
)
