import MagHK.Noninteracting
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Joint and parameter continuity of the integral-defined bounded-example
orbital. The parameter is extended by max(t,0), so the rational denominators
remain strictly positive on the entire parameter space.
-/

noncomputable section
namespace MagHK.ParameterContinuity

open MagHK.Noninteracting
open Filter Set
open scoped Topology

theorem profileA_joint_continuous_extension :
    Continuous (fun p : ℝ × ℝ => profileA (max p.1 0) p.2) := by
  have ht : Continuous (fun p : ℝ × ℝ => max p.1 0) :=
    continuous_fst.max continuous_const
  have hs : Continuous (fun p : ℝ × ℝ => Real.sqrt (1 + p.2 ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_snd.pow 2))
  have hE : Continuous (fun p : ℝ × ℝ =>
      Real.exp (Real.sqrt (1 + p.2 ^ 2) - 1)) :=
    Real.continuous_exp.comp (hs.sub continuous_const)
  have hn : Continuous (fun p : ℝ × ℝ =>
      max p.1 0 * p.2 * Real.exp (Real.sqrt (1 + p.2 ^ 2) - 1) ^ 2) :=
    (ht.mul continuous_snd).mul (hE.pow 2)
  have hd : Continuous (fun p : ℝ × ℝ =>
      1 + max p.1 0 * p.2 ^ 2 * Real.exp (Real.sqrt (1 + p.2 ^ 2) - 1) ^ 2) :=
    continuous_const.add ((ht.mul (continuous_snd.pow 2)).mul (hE.pow 2))
  have hden : ∀ p : ℝ × ℝ,
      1 + max p.1 0 * p.2 ^ 2 * Real.exp (Real.sqrt (1 + p.2 ^ 2) - 1) ^ 2 ≠ 0 := by
    intro p
    have ht0 : 0 ≤ max p.1 0 := le_max_right _ _
    exact ne_of_gt (by positivity)
  have heq : (fun p : ℝ × ℝ => profileA (max p.1 0) p.2) =
      (fun p => max p.1 0 * p.2 * Real.exp (Real.sqrt (1 + p.2 ^ 2) - 1) ^ 2 /
        (1 + max p.1 0 * p.2 ^ 2 * Real.exp (Real.sqrt (1 + p.2 ^ 2) - 1) ^ 2)) := by
    funext p
    exact profileA_regular (max p.1 0) p.2
  rw [heq]
  exact hn.div hd hden

theorem profileU_joint_continuous_extension :
    Continuous (fun p : ℝ × ℝ => profileU (max p.1 0) p.2) := by
  have hh0 : Continuous profileH := continuous_iff_continuousAt.mpr
    (fun r => (profileH_hasDerivAt r).continuousAt)
  have hp0 : Continuous profileHPrime := continuous_iff_continuousAt.mpr
    (fun r => (profileHPrime_hasDerivAt r).continuousAt)
  have hh : Continuous (fun p : ℝ × ℝ => profileH p.2) := hh0.comp continuous_snd
  have hp : Continuous (fun p : ℝ × ℝ => profileHPrime p.2) := hp0.comp continuous_snd
  have hn : Continuous (fun p : ℝ × ℝ =>
      20 * p.2 + p.2 * profileHPrime p.2 + 3 * profileH p.2 +
        p.2 * profileH p.2 ^ 2 + 2 * profileA (max p.1 0) p.2) :=
    ((((continuous_const.mul continuous_snd).add (continuous_snd.mul hp)).add
      (continuous_const.mul hh)).add (continuous_snd.mul (hh.pow 2))).add
      (continuous_const.mul profileA_joint_continuous_extension)
  have hd : Continuous (fun p : ℝ × ℝ => 2 * (1 + p.2 * profileH p.2)) :=
    continuous_const.mul (continuous_const.add (continuous_snd.mul hh))
  have hden : ∀ p : ℝ × ℝ, 2 * (1 + p.2 * profileH p.2) ≠ 0 := by
    intro p
    have hh0 := profileH_mul_nonneg p.2
    exact ne_of_gt (by positivity)
  exact hn.div hd hden

theorem profileF_joint_continuous_extension :
    Continuous (fun p : ℝ × ℝ => profileF (max p.1 0) p.2) := by
  have hi : Continuous (fun p : ℝ × ℝ =>
      ∫ u in (0 : ℝ)..p.2, profileU (max p.1 0) u) :=
    intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := fun t u => profileU (max t 0) u)
      profileU_joint_continuous_extension
  exact Real.continuous_exp.comp hi.neg

theorem profileF_parameter_extension_continuous (r : ℝ) :
    Continuous (fun t : ℝ => profileF (max t 0) r) :=
  profileF_joint_continuous_extension.comp (continuous_id.prodMk continuous_const)

theorem profileF_parameter_continuousOn (r : ℝ) :
    ContinuousOn (fun t : ℝ => profileF t r) (Ici 0) := by
  apply (profileF_parameter_extension_continuous r).continuousOn.congr
  intro t ht
  change 0 ≤ t at ht
  simp only [max_eq_left ht]

theorem profileF_parameter_continuousAt (r t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => profileF s r) t :=
  (profileF_parameter_continuousOn r t (le_of_lt ht)).continuousAt (Ici_mem_nhds ht)

theorem profileF_parameter_tendsto (r t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun s : ℝ => profileF s r) (𝓝[Ici 0] t) (𝓝 (profileF t r)) :=
  profileF_parameter_continuousOn r t ht

theorem profileF_joint_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => profileF p.1 p.2) {p | 0 ≤ p.1} := by
  apply profileF_joint_continuous_extension.continuousOn.congr
  intro p hp
  change 0 ≤ p.1 at hp
  simp only [max_eq_left hp]

end MagHK.ParameterContinuity
