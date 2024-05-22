{-

The properties of the flat modality that we use are built into Agda's --cohesion and
--flat-split flags, so we do not need to postulate anything more, but we mention here
some information about the modality.

The --cohesion flag enables flat-modal hypotheses and flat-modal functions as
described in Section 4 of

  Daniel R. Licata, Ian Orton, Andrew M. Pitts, Bas Spitters.
  Internal Universes in Models of Homotopy Type Theory

The --flat-split flag enables "crisp induction", as described for identity types in the
article above. In the formalization we use crisp induction for identity types, as in the
paper above, and also for coproducts in the module tiny.preserves-coproduct.

-}
module axiom.flat where
