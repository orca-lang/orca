# Orca: A Dependent Type Theory with Contextual Types

Orca a type theory with support for Higher Order Abstract Syntax
(HOAS) by extending Martin-Löf style type theory with contextual
types and a specification framework based on the logical framework LF.

## Examples

To illustrate a simple type preservation proof for the simply typed
lamda calculus check tps.kw in the examples directory.

## Building and running

To build orca simply run ```make``` on the repository and run:
```./orca.byte examples/tps.kw```

## Documentation

Orca is under heavy development, but you can check some information
and the theory in
[this document](https://github.com/orca-lang/orca/raw/master/doc/orcadoc.pdf).
