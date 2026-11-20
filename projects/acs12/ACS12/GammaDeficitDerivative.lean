import ACS12.GammaFractionalMoment

/-! Differential recurrence between consecutive exact hyperbolic deficits. -/
namespace ACS12.GammaDeficit

noncomputable def sinhProfileDerivative (a t : ℝ) : ℝ :=
  -a * Real.cosh (t / 2) * (2 * Real.sinh (t / 2)) ^ (-a - 1)

private theorem twiceSinhHalf_deriv (t : ℝ) :
    HasDerivAt (fun x => 2 * Real.sinh (x / 2)) (Real.cosh (t / 2)) t := by
  convert ((Real.hasDerivAt_sinh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)).const_mul 2 using 1
  norm_num
  ring

theorem sinhProfile_hasDerivAt (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (sinhProfile a) (sinhProfileDerivative a t) t := by
  have hS : 0 < 2 * Real.sinh (t / 2) := mul_pos (by norm_num)
    (Real.sinh_pos_iff.mpr (by positivity))
  convert (twiceSinhHalf_deriv t).rpow_const (p := -a) (Or.inl hS.ne') using 1
  unfold sinhProfileDerivative
  ring

theorem sinhProfileDerivative_hasDerivAt (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (sinhProfileDerivative a)
      (a ^ 2 / 4 * sinhProfile a t + a * (a + 1) * sinhProfile (a + 2) t) t := by
  let s := Real.sinh (t / 2)
  let c := Real.cosh (t / 2)
  let d := 2 * s
  have hs : 0 < s := Real.sinh_pos_iff.mpr (by positivity)
  have hd : 0 < d := mul_pos (by norm_num) hs
  have h₁ := ((Real.hasDerivAt_cosh (t / 2)).comp t ((hasDerivAt_id t).div_const 2)).const_mul (-a)
  have h₂ := (twiceSinhHalf_deriv t).rpow_const (p := -a - 1) (Or.inl hd.ne')
  convert h₁.mul h₂ using 1
  simp only [id_eq,show -a - 1 - 1 = -a - 2 by ring]
  change a ^ 2 / 4 * d ^ (-a) + a * (a + 1) * d ^ (-(a + 2)) =
    (-a * (s * (1 / 2))) * d ^ (-a - 1) + (-a * c) * (c * (-a - 1) * d ^ (-a - 2))
  have hExp₁ : d ^ (-a - 1) = d ^ (-a - 2) * d := by
    rw [← Real.rpow_add_one hd.ne']
    congr 1
    ring
  have hExp₀ : d ^ (-a) = d ^ (-a - 2) * d ^ 2 := by
    rw [← Real.rpow_two,← Real.rpow_add hd]
    congr 1
    ring
  have hCos : c ^ 2 = 1 + s ^ 2 := by
    have h := Real.cosh_sq_sub_sinh_sq (t / 2)
    change c ^ 2 - s ^ 2 = 1 at h
    linarith only [h]
  rw [hExp₀,hExp₁,show -(a + 2) = -a - 2 by ring]
  unfold d
  linear_combination -(a * (a + 1) * (2 * s) ^ (-a - 2)) * hCos

noncomputable def deficitProfileDerivative (a t : ℝ) : ℝ :=
  -a * t ^ (-a - 1) - sinhProfileDerivative a t

theorem deficitProfile_hasDerivAt (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deficitProfile a) (deficitProfileDerivative a t) t :=
  (Real.hasDerivAt_rpow_const (p := -a) (Or.inl ht.ne')).sub (sinhProfile_hasDerivAt a ht)

theorem deficitProfileDerivative_hasDerivAt (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deficitProfileDerivative a)
      (a * (a + 1) * deficitProfile (a + 2) t - a ^ 2 / 4 * sinhProfile a t) t := by
  convert ((Real.hasDerivAt_rpow_const (p := -a - 1) (Or.inl ht.ne')).const_mul (-a)).sub
    (sinhProfileDerivative_hasDerivAt a ht) using 1
  unfold deficitProfile
  rw [show -a - 1 - 1 = -(a + 2) by ring]
  ring

noncomputable def deficitBoundary (a t : ℝ) : ℝ :=
  t * deficitProfileDerivative a t - deficitProfile a t

theorem deficitBoundary_hasDerivAt (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deficitBoundary a)
      (t * (a * (a + 1) * deficitProfile (a + 2) t - a ^ 2 / 4 * sinhProfile a t)) t := by
  convert ((hasDerivAt_id t).mul (deficitProfileDerivative_hasDerivAt a ht)).sub
    (deficitProfile_hasDerivAt a ht) using 1
  simp only [id_eq,one_mul]
  ring

end ACS12.GammaDeficit
