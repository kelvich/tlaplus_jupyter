[![Build status](https://ci.appveyor.com/api/projects/status/myh95n5j0j0pr04j/branch/master?svg=true)](https://ci.appveyor.com/project/kelvich/tlaplus-jupyter/branch/master)
[![Build Status](https://travis-ci.org/kelvich/tlaplus_jupyter.svg?branch=master)](https://travis-ci.org/kelvich/tlaplus_jupyter)
[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/kelvich/tlaplus_jupyter/master?filepath=intro.ipynb)

# tlaplus_jupyter

Jupyter kernel for TLA⁺ and Pluscal specification languages.
* Syntax highlight based on official lexer.
* REPL functionality for expressions.
* Can be executed online with Binder. [Try it now!](https://mybinder.org/v2/gh/kelvich/tlaplus_jupyter/master?filepath=intro.ipynb)
* No need to install TLA Toolbox: Java and Python will be enough.

<p align="center">
  <img width="1227" alt="Screenshot 2019-11-11 at 23 58 17" src="https://user-images.githubusercontent.com/284219/68620766-3d3f5400-04df-11ea-8fa7-763124f84162.png">
</p>

## Installation

`tlaplus_jupyter` is a python package installable with `pip`. Python 2 and 3 are supported. To install run:

```
pip install tlaplus_jupyter
python -m tlaplus_jupyter.install
```

The last step will register `tlaplus_jupyter` as a Jupyter kernel in your system and will download `tla2tools.jar`. After that Jupyter can be started as usual:

```
jupyter notebook
```

To create a new TLA⁺ notebook click on the `New` button and select TLA⁺ in a dropdown menu. It is also handy to enable line numbering inside cells (View > Toggle Line Numbers) since syntax checker refers to problems by their line numbers.

## Usage

Basic usage is explained in an [intro notebook](https://mybinder.org/v2/gh/kelvich/tlaplus_jupyter/master?filepath=intro.ipynb).

`tlaplus_jupyter` supports several types of cells with different behavior on execution:

1. Cells with `full module definition`. Upon execution kernel will perform syntax check (with tla2sany.SANY) and report errors if any. If the module contains Pluscal program kernel will also translate it to TLA.

2. Cell starting with `%tlc:ModuleName` where `ModuleName` is the name of one of the modules previously executed. In this case, the cell is treated as a config file for the TLC model checker. For example to check spec `Spec` and invariant `TypeOk` of model `DieHardTLA` execute following:
    ```
    %tlc:DieHardTLA
    SPECIFICATION Spec
    INVARIANT TypeOK
    ```

    Init and next state formula can be set after keywords `INIT` and `NEXT` correspondingly. Constant definitions should follow `CONSTANTS` keyword separated by newline or commas. Description of possible config statements and syntax is given in chapter 14 of [Specifying systems](https://www.microsoft.com/en-us/research/publication/specifying-systems-the-tla-language-and-tools-for-hardware-and-software-engineers/) book.

    Custom TLC flags may be specified after the module name:
    ```
    %tlc:DieHardTLA -deadlock
    SPECIFICATION Spec
    ```

    TLC evaluation happens in the context of all defined modules. So if model refers to another model that other model should be at some cell too.

3. Cells containing neither `%`-magic nor module definition are treated as a constant expression and will print its results on execution. As with `!tlc` evaluation happens in the context of all defined modules, so the expression can refer to anything defined in evaluated modules.

4. Command `%log` / `%log on` / `%log off` correspondingly shows kernel log / enables logging / disables logging for currently open notebook.

## Sharing executable models with Binder

TLA⁺ models shared on Github can be easily made runnable by coping  [Dockerfile](Dockerfile) to the repository root. After that, URL to such repo can be used at [Binder](https://mybinder.org) to start a dynamic TLA⁺ environment.

## Related Projects

[vscode-tlaplus](https://github.com/alygin/vscode-tlaplus) Cool plugin for VSCode editor with syntax highlight and custom widgets for displaying traces.

## License

[BSD](LICENSE)
