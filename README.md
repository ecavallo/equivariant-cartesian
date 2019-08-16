# Orton-Pitts-style formalization of an equivariant cartesian cubical set model of type theory

This code is an extension of [the code accompanying Ian Orton's thesis](https://www.repository.cam.ac.uk/handle/1810/288558) (along with a few modifications introduced in [gen-cart](https://github.com/mortberg/gen-cart)). It describes a construction of a model of univalent type theory from a locally cartesian closed category (LCCC) satisfying certain axioms. As described by Orton and Pitts [4], the code is to be read in the internal language of the LCCC (namely, extensional type theory). We also adapt the construction of a universe of fibrations due to Licata, Orton, Pitts, and Spitters [3].

We extend the work of Orton and Pitts to accommodate cartesian cubical set models [1,2] with an additional *equivariance* condition on fibrations, as developed by Steve Awodey, Evan Cavallo, Thierry Coquand, Emily Riehl, and Christian Sattler. The ultimate objective is to produce a constructive model structure which is classically Quillen equivalent to that of spaces. This formalization is one piece of that argument: it shows that this notion of fibration can be used to interpret type theory. The interpretation can then be used as a tool to construct a model structure, as in [2,5].

The axioms required of the ambient category can be found in the `axioms` folder. The significant changes, relative to the "standard" cartesian cubical set model, are all in `shape`, `cofprop`, and `tiny`. We assume a type `Shape` of composition shapes, with decoding `⟨_⟩ : Shape → Set`, and a type of shape morphisms. A fibration (as defined in `fibrations`) provides composites from `r : ⟨ S ⟩` to `s : ⟨ S ⟩` for every shape `S` in a way stable under shape morphisms (i.e., equivariantly). The standard cartesian cubical set model is recovered by taking `Shape` to have a single object which decodes to the interval and only identity morphisms. The intended equivariant model is obtained by taking `Shape` to be the restriction of the cube category to isomorphisms.

The construction of the universe is currently not quite complete; we have not shown that it is fibrant. However, this should be a more-or-less straightforward consequence of the Fibration Extension Property, which we have proven (`fibration-extension`).

Warning: Some files, particularly `glueing.weak` and `fibration-extension`, take a long time to check.

[1] Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Kuen-Bang Hou (Favonia), Robert Harper, and Daniel R. Licata. Syntax and Models of Cartesian Cubical Type Theory. 2019. https://github.com/dlicata335/cart-cube.

[2] Steve Awodey. A Quillen model structure on the category of cartesian cubical sets. 2019. https://github.com/awodey/math/blob/master/QMS/qms.pdf.

[3] Daniel R. Licata, Ian Orton, Andrew M. Pitts, and Bas Spitters. Internal Universes in Models of Homotopy Type Theory. In FSCD, volume 108 of LIPIcs, pages 22:1–22:17. Schloss Dagstuhl - Leibniz-Zentrum fuer Informatik. 2018.

[4] Ian Orton and Andrew M. Pitts. Axioms for Modelling Cubical Type theory in a Topos. In Logical Methods in Computer Science, Volume 14, Issue 4. 2018.

[5] Christian Sattler. The equivalence extension property and model structures. 2017. https://arxiv.org/abs/1704.06911v3.
