import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic.FunProp

/-! Rotational invariance of the angular measure obtained by radial projection
of actual Lebesgue measure in the unit ball. No spherical quadrature is assumed. -/
noncomputable section
namespace MagHK.MonopoleSphere

open MeasureTheory Metric Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def normalize (x : E) : E := ‖x‖⁻¹ • x

theorem normalize_measurable : Measurable (normalize : E → E) := by
  unfold normalize
  fun_prop

theorem normalize_isometry (R : E ≃ₗᵢ[ℝ] E) (x : E) :
    normalize (R x) = R (normalize x) := by
  simp only [normalize, R.norm_map, map_smul]

def angularBallMeasure : Measure E :=
  (3 : ℝ≥0∞) • Measure.map normalize (volume.restrict (ball (0 : E) 1))

theorem ball_measurePreserving (R : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving R (volume.restrict (ball (0 : E) 1))
      (volume.restrict (ball (0 : E) 1)) := by
  have h := R.measurePreserving.restrict_preimage_emb
    R.toMeasurableEquiv.measurableEmbedding (ball (0 : E) 1)
  have he : R ⁻¹' ball (0 : E) 1 = ball (0 : E) 1 := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, R.norm_map]
  rwa [he] at h

theorem angularBallMeasure_invariant (R : E ≃ₗᵢ[ℝ] E) :
    Measure.map R angularBallMeasure = angularBallMeasure := by
  have hcomm : R ∘ normalize = normalize ∘ R :=
    funext (fun x => (normalize_isometry R x).symm)
  rw [angularBallMeasure, Measure.map_smul,
    Measure.map_map R.continuous.measurable normalize_measurable, hcomm,
    ← Measure.map_map normalize_measurable R.continuous.measurable,
    (ball_measurePreserving R).map_eq]

theorem angularBall_measurePreserving (R : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving R angularBallMeasure angularBallMeasure :=
  ⟨R.continuous.measurable, angularBallMeasure_invariant R⟩

end MagHK.MonopoleSphere
