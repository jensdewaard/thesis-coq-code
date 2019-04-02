# Jens de Waard MSc Thesis Project 

So far, the project has the following files:

##AbstractBool.v
This file defines the abstract values for booleans as well as the abstract
versions of the negation, and and or functions.

##Parity.v
This file defines the abstract interpretation of natural numbers as their
parity (even or odd) and provides abstract versions of addition and
multiplication.

##Language.v 
This file describes the possible statements and expressions in the language
we're writing proofs about.

##Preorder.v
This file defines the PreorderedSet typeclass and provides several instances
for it. It also includes the definition of what it means for a function to be
monotone.

##Abstract and ConcreteInterpreter
These contain the evalutation functions for the language specified in
Language.v.

##Maps.v
An implementation for maps, taken from the SoftwareFoundations book.

##AbstractStore.v
Contains the definitions for both the concrete and the abstract stores, which
are based on maps.

##Galois.v
This file gives the definition of the Galois typeclass and provides the
necessary instances of the typeclass for the soundness theorems.

##Monad.v
Defines what a Monad is as a typeclass and provides an imlementation of the 
typeclass in the form of a State monad. 

##Soundness
Contains the various soundness lemma's and the proofs of the soundness of the
abstract interpreter wrt the concrete interpreter.
