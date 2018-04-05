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

## Requirements

Python3.

* z3
* pygment (for exception pretty printing)
* posix_ipc
