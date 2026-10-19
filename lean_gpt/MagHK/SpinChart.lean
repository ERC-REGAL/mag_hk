import MagHK.SpinGroup
import MagHK.MonopoleHilbert
import MagHK.MonopoleGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! A literal Hopf-chart formula for the rotation action on charged sections.
The universal integration theorem for covariant angular momentum is recorded
separately from the calculations for the selected charge and ground state. -/
noncomputable section
namespace MagHK.SpinChart
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.MonopoleTrial
open scoped ComplexConjugate
abbrev Space := WithLp 2 (ℝ × ℂ)

def spinor (p : Angle) : Fin 2 → ℂ :=
  ![(Real.sqrt ((1 + p.1) / 2) : ℂ),
    MagHK.Spin.phase (-p.2) * (Real.sqrt ((1 - p.1) / 2) : ℂ)]

def hopf (z : Fin 2 → ℂ) : Space := WithLp.toLp 2
  (Complex.normSq (z 0) - Complex.normSq (z 1), 2 * z 0 * conj (z 1))

def movedSpinor (U : MagHK.Spin.Group) (p : Angle) : Fin 2 → ℂ :=
  (U⁻¹).val.mulVec (spinor p)

def movedAngle (U : MagHK.Spin.Group) (p : Angle) : Angle :=
  (2 * Complex.normSq (movedSpinor U p 0) - 1,
    -Complex.arg (movedSpinor U p 1 / movedSpinor U p 0))

def movedChart (U : MagHK.Spin.Group) (x : Chart) : Chart := (x.1, movedAngle U x.2)

def unitPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

def gaugePhase (q : ℤ) (U : MagHK.Spin.Group) (p : Angle) : ℂ :=
  unitPhase (movedSpinor U p 0) ^ q

def actionWave (q : ℤ) (U : MagHK.Spin.Group) (f : Chart → ℂ) (x : Chart) : ℂ :=
  gaugePhase q U x.2 * f (movedChart U x)

def actionPairWave (q : ℤ) (U : MagHK.Spin.Group)
    (f : Chart × Chart → ℂ) (p : Chart × Chart) : ℂ :=
  gaugePhase q U p.1.2 * gaugePhase q U p.2.2 *
    f (movedChart U p.1, movedChart U p.2)

theorem unitPhase_norm (z : ℂ) : ‖unitPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [unitPhase, hz]
  · simp [unitPhase, hz, norm_div, norm_norm, norm_ne_zero_iff.mpr hz]

theorem gaugePhase_norm (q : ℤ) (U : MagHK.Spin.Group) (p : Angle) :
    ‖gaugePhase q U p‖ = 1 := by
  simp [gaugePhase, norm_zpow, unitPhase_norm]

theorem actionWave_norm (q : ℤ) (U : MagHK.Spin.Group) (f : Chart → ℂ) (x : Chart) :
    ‖actionWave q U f x‖ = ‖f (movedChart U x)‖ := by
  simp [actionWave, norm_mul, gaugePhase_norm]

theorem actionPairWave_norm (q : ℤ) (U : MagHK.Spin.Group)
    (f : Chart × Chart → ℂ) (p : Chart × Chart) :
    ‖actionPairWave q U f p‖ = ‖f (movedChart U p.1, movedChart U p.2)‖ := by
  simp [actionPairWave, norm_mul, gaugePhase_norm]

theorem action_determinant (q : ℤ) (U : MagHK.Spin.Group) (f g : Chart → ℂ) :
    actionPairWave q U (determinant f g) =
      determinant (actionWave q U f) (actionWave q U g) := by
  funext p
  simp only [actionPairWave, determinant, actionWave,
    MagHK.Slater.slaterSlice, MagHK.Slater.determinantSlice]
  ring

/-- The result of integrating covariant angular-momentum operators for an
arbitrary integral monopole charge. Actions are identified with the explicit
local gauge pullback above. The geometric rotation is an actual proper
linear isometry, and the covering property is explicit. -/
structure AngularMomentumAction (q : ℤ) where
  one : MagHK.Spin.Group →* Module.End ℂ State
  pair : MagHK.Spin.Group →* Module.End ℂ FermionState
  one_norm : ∀ U ψ, ‖one U ψ‖ = ‖ψ‖
  pair_norm : ∀ U ψ, ‖pair U ψ‖ = ‖ψ‖
  one_formula : ∀ U ψ, ∀ᵐ x ∂chartMeasure,
    one U ψ x = actionWave q U ψ x
  pair_formula : ∀ U ψ, ∀ᵐ p ∂pairMeasure,
    (pair U ψ).val p = actionPairWave q U ψ.val p
  rotation : MagHK.Spin.Group → Space ≃ₗᵢ[ℝ] Space
  rotation_proper : ∀ U, LinearMap.det (rotation U).toLinearEquiv.toLinearMap = 1
  rotation_cover : ∀ R : Space ≃ₗᵢ[ℝ] Space,
    LinearMap.det R.toLinearEquiv.toLinearMap = 1 → ∃ U, rotation U = R
  rotation_hopf : ∀ U z, hopf (U.val.mulVec z) = rotation U (hopf z)
  chart_measure : ∀ U, MeasurePreserving (movedChart U) chartMeasure chartMeasure

/-- Standard unitary integration and chart realization for the family of
covariant angular-momentum operators. This premise is uniform in charge and
has no Hamiltonian eigenfunction, ground-state or current conclusion. -/
def StandardAngularMomentumLibrary : Prop := ∀ q : ℤ, Nonempty (AngularMomentumAction q)

end MagHK.SpinChart
