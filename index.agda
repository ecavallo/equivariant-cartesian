{-

------------------------------------------------------------------------------------------
Formalization of an equivariant cartesian cubical set model of type theory
------------------------------------------------------------------------------------------

This formalization accompanies the article

  The equivariant model structure on cartesian cubical sets.
  Steve Awodey, Evan Cavallo, Thierry Coquand, Emily Riehl, and Christian Sattler

The contents of the formalization are summarized in Appendix A of the article.

The formalization defines a model of homotopy type theory inside an extensional type
theory augmented with a flat modality and axioms postulating *shapes* (among them an
*interval*) and a cofibration classifier. The results can in particular be externalized in
the category of cartesian cubical sets.

The code has been tested with Agda version 2.6.4.
The source is available at

  github.com/ecavallo/equivariant-cartesian

and there is an HTML interface at

  ecavallo.github.io/equivariant-cartesian

For reference (see the file equivariant.agda-lib in the source), the formalization is
compiled with the flags

  --with-K
  --cohesion --flat-split
  --no-import-sorts
  --rewriting

In particular, the --with-K flag enables axiom K (uniqueness of identity proofs), while
the --cohesion and --flat-split flags enable the flat modality.

-}

module index where

--↓ The summary module defines the interpretation of homotopy type theory: the judgments,
--↓ type formers (including universes), and the univalence axiom. Most of the results are
--↓ imported from elsewhere in the formalization.

import summary

--↓ The prelude: basic constructs of the ambient type theory, such as sigma types, natural
--↓ numbers, isomorphisms, etc.

import basic

--↓ Syntax for the internal model of *extensional* type theory where contexts are
--↓ interpreted as types and types as families in some universe.

import internal-extensional-type-theory

--↓ Axioms postulated for the construction.

import axiom

--↓ Basic properties of the cofibration classifier.

import cofibration

--↓ Consequences of the axioms expressing tinyness of shapes.

import tiny

--↓ Properties of and operations on fibrations.

import fibration

--↓ Interpretations of the type formers.

import type-former

--↓ Interpretation of the universe type and the univalence axiom.

import universe
