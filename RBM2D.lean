import RBM2D.Basic
import RBM2D.Test.Axioms
import RBM2D.Defs.Block
import RBM2D.Defs.Dist
import RBM2D.Defs.Domination
import RBM2D.Propagator.Basic
import RBM2D.Propagator.Bounds
import RBM2D.Propagator.Symbol
import RBM2D.Propagator.Elliptic
import RBM2D.Propagator.Momentum
import RBM2D.Propagator.Shells
import RBM2D.Propagator.GeomSum
import RBM2D.Propagator.Dyadic
import RBM2D.Propagator.ZeroMode
import RBM2D.Propagator.Harmonic
import RBM2D.Delocalization
import RBM2D.Gauss.Envelope

/-! Hard axiom audit of the whole library: see `RBM2D.Test.Axioms`. -/
#assert_rbm_axioms
