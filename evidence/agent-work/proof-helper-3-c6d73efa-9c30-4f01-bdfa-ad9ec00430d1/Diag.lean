import Proofs.EvaluationWithOneProjection

set_option Elab.async false
set_option maxHeartbeats 2000000
namespace OverlapLeft
open MackeyDiagrams MackeyDiagrams.Generator
open scoped BigOperators
noncomputable section

variable {U : Type} [Group U] {D E B : Subgroup U}
local notation "T" => (⊥ : Subgroup U)

abbrev a {U : Type} [Group U] : ConjEmbedding (⊥ : Subgroup U) ⊥ := ConjEmbedding.id _
def dot {H : Subgroup U} {α β : ConjEmbedding T H} (z : H) : Dot α β :=
  ⟨z, fun y => by
    have hy : y = 1 := Subtype.ext (Subgroup.mem_bot.mp y.property)
    simp [hy]⟩

variable (u : ConjEmbedding T B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
variable (b : ConjEmbedding T D) (e : ConjEmbedding T E)

abbrev lo (u : ConjEmbedding T B) (v : ConjEmbedding D B) (b : ConjEmbedding T D) : Dot (u.comp a) (v.comp b) := dot 1
abbrev hi (u : ConjEmbedding T B) (w : ConjEmbedding E B) (e : ConjEmbedding T E) : Dot (u.comp a) (w.comp e) := dot 1
abbrev mid (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (b : ConjEmbedding T D) (e : ConjEmbedding T E) (r : D) (s : E) : Dot (v.comp b) (w.comp e) :=
  dot ((v.toHom r)⁻¹ * w.toHom s)

abbrev targetPair (e : ConjEmbedding T E) : Word T E := (Word.up (a (U := U))).tensor (Word.down e)
abbrev targetRep (e : ConjEmbedding T E) (y : E) : (targetPair e).basis.carrier :=
  Biset.pair (Word.up a).basis (Word.down e).basis (1 : T) y

abbrev q (u : ConjEmbedding T B) (w : ConjEmbedding E B) (e : ConjEmbedding T E) (p : (targetPair e).basis.carrier) :=
  mixedProduct u w (mixedMultiplicationBasis u w a e (hi u w e) p)

#check lo
#check hi
#check mid
#check targetRep
#check q
end
end OverlapLeft
