# Jens de Waard MSc Thesis Project 

## Building the project

Requirements 
- A recent version of Coq (probably 8.9 or higher)
- GNU Make

Run make in the root directory of the project, which is the directory 
containing this README and the _CoqProject file. This will compile all 
the source files. It is then possible to step through the proofs
using an IDE such as CoQIDE or ProofAssistant.

## Source Files

This is a list of the various files in the project, and where they are
in the thesis document.

| Source Files          | Thesis Chapter | Description                                         |
| --------------------- | -------------- | --------------------------------------------------- |
| Language/*            | Chapter 3      | Syntax of the interpreted language.                 |
| Types/*               | Chapter 3      | Abstract versions of the concrete types.            |
| Classes/*             | Chapter 4      | The typeclasses used to decompose the interpreters. |
| Instances/*           | Chapter 4      | Instances of those typeclasses.                     |
| GenericInterpreter.v  | Chapter 4      | The layout of the generic interpreter.              |
| Soundness.v           | Chapter 4      | Proof that the generic interpreter is sound.        |