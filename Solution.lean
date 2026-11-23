module

public import RBM2D

public section

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `RBM2D` named in its proof. The
definitions that occur in the statements are those of `RBM2D/MainDefs.lean`.
-/

section
namespace RBM.Endpoints

/-- Theorem 2.2: delocalization of the bulk eigenvectors; the statement is `RBM.Endpoints.decol`. -/
theorem theorem_2_2 : decol :=
  decol_holds

/-- Theorem 2.3: the local semicircle law, (4) and (5); the statement is `RBM.Endpoints.locSC`. -/
theorem theorem_2_3 : locSC :=
  locSC_holds

/-- Theorem 2.4: generalized quantum unique ergodicity, (8) and (9); the statement is `RBM.Endpoints.QUE`. -/
theorem theorem_2_4 : QUE :=
  QUE_holds

/-- Theorem 2.5: quantum diffusion, (10)–(13); the statement is `RBM.Endpoints.QDiff`. -/
theorem theorem_2_5 : QDiff :=
  QDiff_holds

end RBM.Endpoints
end
