import MagHK.Cartesian

/-! Actual Cartesian curvature at the axis for both vector potentials. -/

noncomputable section
namespace MagHK.Cartesian

open scoped ContDiff

def planarCurl (A : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => (A (x, p.2)).2) p.1 -
    deriv (fun y => (A (p.1, y)).1) p.2

theorem azimuthal_curl_origin (C : ℝ × ℝ → ℝ) (hC : ContDiff ℝ ∞ C) :
    planarCurl (fun p => (-p.2 * C p, p.1 * C p)) (0, 0) = 2 * C (0, 0) := by
  have hx : DifferentiableAt ℝ (fun x : ℝ => C (x, 0)) 0 :=
    (hC.comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by norm_num) 0
  have hy : DifferentiableAt ℝ (fun y : ℝ => C (0, y)) 0 :=
    (hC.comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by norm_num) 0
  have hdx := ((hasDerivAt_id (0 : ℝ)).mul hx.hasDerivAt).deriv
  have hdy := ((hasDerivAt_id (0 : ℝ)).neg.mul hy.hasDerivAt).deriv
  simp only [Pi.neg_apply, id_eq, zero_mul, one_mul, neg_one_mul, neg_zero, add_zero] at hdx hdy
  change deriv (fun x => x * C (x, 0)) 0 = C (0, 0) at hdx
  change deriv (fun y => -y * C (0, y)) 0 = -C (0, 0) at hdy
  change deriv (fun x => x * C (x, 0)) 0 - deriv (fun y => -y * C (0, y)) 0 = _
  rw [hdx, hdy]
  ring

theorem gaussian_curl_origin (t : ℝ) (ht : 0 ≤ t) :
    planarCurl (gaussianVector t) (0, 0) = 2 * t := by
  unfold gaussianVector
  rw [azimuthal_curl_origin _ (gaussianCoefficient_contDiff t ht)]
  simp [gaussianCoefficient, radiusSq]

theorem bounded_curl_origin (t : ℝ) (ht : 0 ≤ t) :
    planarCurl (boundedVector t) (0, 0) = 2 * t := by
  unfold boundedVector
  rw [azimuthal_curl_origin _ (boundedCoefficient_contDiff t ht)]
  simp [boundedCoefficient, radialExponential, radiusSq]

theorem gaussian_curl_nonzero (t : ℝ) (ht : 0 < t) :
    planarCurl (gaussianVector t) ≠ 0 := by
  intro h
  have hz := congrFun h (0, 0)
  rw [gaussian_curl_origin t ht.le] at hz
  change 2 * t = 0 at hz
  linarith

theorem bounded_curl_nonzero (t : ℝ) (ht : 0 < t) :
    planarCurl (boundedVector t) ≠ 0 := by
  intro h
  have hz := congrFun h (0, 0)
  rw [bounded_curl_origin t ht.le] at hz
  change 2 * t = 0 at hz
  linarith

end MagHK.Cartesian
