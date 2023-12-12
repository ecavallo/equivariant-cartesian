# Contents of the formalization

Ordered roughly by conceptual priority.

* `prelude`: 

  Basic definitions.

* `axioms`: Imports the following modules, which postulate various axioms.

  * `axioms.funext`:
  
    Postulates function extensionality for the extensional type theory.
      
  * `axioms.truncation`:
  
    Postulates a propositional truncation type former for the extensional type theory.
      
  * `axioms.realignment`:
  
    Postulates the realignment axiom for the universes of the extensional type theory.
  
  * `axioms.shape`:
    
    Postulates a type `Shape` of codes for shapes and, for every pair of shapes `S` and `T`, a type
    `ShapeHom S T` of codes for homomorphisms between them.  Postulates functions `⟨_⟩` and `⟪_⟫`
    that decodes shapes to types and shape homomorphisms to functions between them.
    
    Postulates an interval shape `int` whose decoding (`Int`) has two distinct points (`O` and `I`).
    
  * `axioms.cofprop`:
  
    Postulates a type `Cof` of codes for propositional cofibrations and a decoding function `[_]`
    that sends codes to propositions (of the extensional type theory).  Postulates cofibration
    formers for equality in a shape, disjunction, and universal quantification over a shape.
    
    Also defines notation and helper functions for working with partial elements (elements of a type
    defined under the assumption that some cofibration is true).
    
  * `axioms.tiny`:
  
    For each shape `S`, postulates an external right adjoint `√ S` to exponentiation by `S`.
    This module uses the flat modality.

* `fibration`: Defines and proves properties of equivariant fibrations, organized as follows:

  * `fibration.fibration`:
  
    Defines equivariant fibrations and proves some basic properties.
    
  * `fibration.realignment`:
  
    Proves that a fibration structure can be realigned along a cofibration.

* `type-formers`: Defines the interpretation of various type formers in the fibration model.

  * `type-formers.empty`
  
  * `type-formers.unit`

  * `type-formers.extension`
  
  * `type-formers.paths`
  
  * `type-formers.sigma`
  
  * `type-formers.pi`
  
  * `type-formers.equivs`:
  
    Derives contractibility, fiber, and equivalence type formers with fibration structures
    using existing type formers.
    
    Constructs the identity equivalence and coercion equivalence (for any fibration `A : ⟨ S ⟩ →
    Type` indexed by a shape and `r s : ⟨ S ⟩`), there is an equivalence between `A r` and `A s`)

  * `type-formers.glue`: Defines the interpretation of `Glue` types, i.e. proves that equivalences extend
    along generating trivial cofibrations.

    * `type-formers.glue.weak`: TODO explain

    * `type-formers.glue.strict`: TODO explain

    * `type-formers.glue.aligned`: TODO explain

    * TODO: state and prove univalence

* `universe`: Definition of a universe classifying equivariant fibrations. This construction uses
  the external tinyness of shapes (`axioms.tiny`) and thus the flat modality.

  * `universe.core`: Defines the universe type `U` and decoding family `El`, proves that `El` is a fibration,
    and constructs an isomorphism between maps `Γ → U` and equivariant fibrations over `Γ`.
    
  * `universe.type-formers`: Uses the results of the `type-formers` directory to show that the
    universe is closed under various type formers.
    
  * TODO: fibrancy of the universe
  
* `remarks`: Miscellaneous observations not used in the main development

  * `shape-to-coproduct`: A proof that dependent exponentiation by a shape commutes with binary
    coproducts, using only external tinyness.
