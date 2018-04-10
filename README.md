# mini-symex

## Overview

Mini symbolic execution engine in Python3, to illustrate some basic ideas of
symbolic execution.

This work is based on these tutorials, I adapt ideas and several code from them.

* [mini-mc, by Xi Wang](http://github.com/xiw/mini-mc)
* [MIT 6.858 Lab 3](https://css.csail.mit.edu/6.858/2015/labs/lab3.html)

## Ingredients

* Concolic execution engine.
* Symbolic execution engine.
* Some arithmetic checks (overflow, divided-by-zero).
* List out-of-bound check.

## Tests

Tests are started with `test_` in `src` folder, execute them to have fun!

## Design

The code can be divided into three categories. AST, concolic values and
execution engine.

### AST

See `ast_base` in `ast.py`. Every subclass of `ast_base` should implement
`z3expr` to support generating z3 expression from this AST node.

### Concolic Values

We have two types of concolic values, see `concolic_int` and `concolic_bool`
in `concolic.py`. `concolic_int` inherits `int`, so we can track operations
on symbolic input. `concolic_bool` is designed as a function, which creates
a path constraint when we generate a new bool.

### Execution Engine

For the first round of execution, we assign zeroes to all concolic values.
After this round is done, we flip every path constraint in the constraint
set, then together use all constraints before that to let z3 generate a
new interesting input.

We use `eval_pc` to prioritize the promising path.

## Requirements

Python3.

* z3
* pygment (for exception pretty printing)
* posix_ipc
