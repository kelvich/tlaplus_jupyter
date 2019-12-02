# coding: utf-8

from setuptools import setup

with open('README.md') as f:
    readme = f.read()

setup(
    name='tlaplus_jupyter',
    version='0.1.1',
    packages=['tlaplus_jupyter'],
    description='Jupyter kernel for TLA⁺',
    author='Stas Kelvich',
    author_email='stas.kelvich@gmail.com',
    url='https://github.com/kelvich/tlaplus_jupyter',
    keywords=['jupyter', 'tla', 'tlaplus', 'pluscal'],
    long_description=readme,
    long_description_content_type="text/markdown",
    include_package_data=True,
    python_requires=">=2.6, !=3.0.*, !=3.1.*, !=3.2.*, !=3.3.*, !=3.4.*",
    test_suite='tests',
    install_requires=[
        # Whole 'notebook' package is not actually needed -- only 'jupyter-client' is
        # mandatory. But dependency on 'notebook' simplifies installation.
        'notebook>=5',
        'ipykernel>=4.10',
        'future>=0.16',
        'psutil>=4'
    ],
    zip_safe=False,
    license='BSD',
    platforms='Platform Independent',
    classifiers=[
        'Topic :: Software Development :: Interpreters',
        'Topic :: Software Development :: Quality Assurance',
        'Topic :: Scientific/Engineering :: Mathematics'
    ]
)
