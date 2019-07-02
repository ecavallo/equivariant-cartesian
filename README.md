# Formalization of an equivariant cartesian cubical set model of type theory

This code is adapted from [the code accompanying Ian Orton's thesis](https://www.repository.cam.ac.uk/handle/1810/288558) along with a few modifications from [gen-cart](https://github.com/mortberg/gen-cart). It follows the approach of Orton and Pitts[3] to constructing models of univalent type theory: the code is to be interpreted in the internal language of a category interpreting extensional type theory, and gives a construction of the model of univalent type theory from a collection of axioms. This construction, in particular, is a variation on existing cartesian cubical set model constructions [1,2] based on an *equivariant* definition of fibration {{idea credit, in what form you desire, goes here}}.

The axioms required of the ambient category can be found in `postulate` blocks in the `prelude`, `shape`, `cofprop`, and `strictness-axioms` files. (The changes, relative to the "standard" cartesian cubical set model, are all in `shape` and `cofprop`). We assume a type `Shape` of composition shapes, with decoding `⟨_⟩ : Shape → Set`, and a type of shape morphisms. A fibration provides composites from `r : ⟨ S ⟩` to `s : ⟨ S ⟩` for every shape `S` in a way stable under shape morphisms (i.e., equivariantly). The standard cartesian cubical set model is recovered by taking `Shape` to have a single object which decodes to the interval and only identity morphisms. 

We do not handle the construction of a fibrant universe of fibrations, which would require the use of *crisp type theory* as described by Licata et al. [4]. We do show in `large-composition` that open boxes of fibrations have composites, using the usual construction from `Glue` types; this would be used to prove the fibrancy of such a universe. (This part is incomplete, as we have not shown the stability of the type composites under reindexing.)

Note: Some files, particularly `glueing.core`, take time to check (up to a minute on my machine). This is mostly spent checking that the fibration structures for the type formers are stable under reindexing, which is generally true up to definitional equality but time-consuming for Agda to check.

[1] Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Kuen-Bang Hou (Favonia), Robert Harper, and Daniel R. Licata. Syntax and Models of Cartesian Cubical Type Theory. 2019. https://github.com/dlicata335/cart-cube

[2] Steve Awodey. A Quillen model structure on the category of cartesian cubical sets. 2019. https://github.com/awodey/math/blob/master/QMS/qms.pdf

[3] Ian Orton and Andrew M. Pitts. Axioms for Modelling Cubical Type theory in a Topos. In Logical Methods in Computer Science, Volume 14, Issue 4. 2018.

[4] Daniel R. Licata, Ian Orton, Andrew M. Pitts, and Bas Spitters. Internal Universes in Models of Homotopy Type Theory. In FSCD, volume 108 of LIPIcs, pages 22:1–22:17. Schloss Dagstuhl - Leibniz-Zentrum fuer Informatik. 2018.
