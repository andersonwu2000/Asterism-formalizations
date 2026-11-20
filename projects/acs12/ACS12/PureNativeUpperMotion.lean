import ACS12.PureNativeExponentUpperBand

/-! Complete spatial motion of the two native curvature blocks at p = 9/5. -/

namespace ACS12.GammaMeasure

open Set

noncomputable def upperNativeRatio (u : ℝ) : ℝ := adjacentRatio u (9 / 5)
noncomputable def upperNativeRatioD (u : ℝ) : ℝ := (4608 / 8575) * u
noncomputable def upperNativeY (u : ℝ) : ℝ := (9 / 5) * nativeS u - 1
noncomputable def upperNativeQ (u : ℝ) : ℝ := upperNativeRatio u * nativeL u
noncomputable def upperNativeQD (u : ℝ) : ℝ := upperNativeRatioD u * nativeL u - upperNativeRatio u / u
noncomputable def nativeAD (u : ℝ) : ℝ := (6 / 25) * (2 - 2 * u - u ^ 2) / (1 + u) ^ 2

noncomputable def upperNativeH (u : ℝ) : ℝ :=
  nativeS u * (2 * upperNativeQ u - 3 / 10) +
    upperNativeY u * nativeL u * (upperNativeQ u - 3 / 10)

noncomputable def upperNativeHD (u : ℝ) : ℝ :=
  (6 / 25) * (2 * upperNativeQ u - 3 / 10) +
    (54 / 125) * nativeL u * (upperNativeQ u - 3 / 10) -
    (upperNativeY u / u) * (upperNativeQ u - 3 / 10) +
    upperNativeQD u * (2 * nativeS u + upperNativeY u * nativeL u)

noncomputable def upperNativeE (u : ℝ) : ℝ :=
  (1 + (9 / 5) * nativeA u) * nativeT u ^ 2 - 2 * nativeA u * nativeT u

noncomputable def upperNativeED (u : ℝ) : ℝ :=
  ((9 / 5) * nativeT u ^ 2 - 2 * nativeT u) * nativeAD u +
    (2 * (1 + (9 / 5) * nativeA u) * nativeT u - 2 * nativeA u) / (1 + u)

noncomputable def upperNativeF (u : ℝ) : ℝ :=
  (1 + (9 / 5) * nativeA u) * nativeT u - nativeA u

noncomputable def upperNativeFD (u : ℝ) : ℝ :=
  ((9 / 5) * nativeT u - 1) * nativeAD u + (1 + (9 / 5) * nativeA u) / (1 + u)

noncomputable def upperNativeUnshifted (u : ℝ) : ℝ := u ^ (-(9 : ℝ) / 5) * upperNativeH u
noncomputable def upperNativeShifted (u : ℝ) : ℝ :=
  (1 + u) ^ (-(9 : ℝ) / 5) * (upperNativeRatio u * upperNativeE u + (3 / 10) * upperNativeF u)

noncomputable def upperNativeUnshiftedD (u : ℝ) : ℝ :=
  u ^ (-(9 : ℝ) / 5) * (upperNativeHD u - (9 / 5) * upperNativeH u / u)

noncomputable def upperNativeShiftedD (u : ℝ) : ℝ :=
  (1 + u) ^ (-(9 : ℝ) / 5) * (upperNativeRatioD u * upperNativeE u +
    upperNativeRatio u * upperNativeED u + (3 / 10) * upperNativeFD u -
    (9 / 5) * (upperNativeRatio u * upperNativeE u + (3 / 10) * upperNativeF u) / (1 + u))

theorem pureNativeBandDD_upper_eq (u : ℝ) :
    pureNativeBandDD u (9 / 5) = upperNativeUnshifted u + upperNativeShifted u := by
  unfold pureNativeBandDD pureNativeG2 pureNativeG1 upperNativeUnshifted upperNativeShifted
    upperNativeH upperNativeQ upperNativeY upperNativeRatio upperNativeE upperNativeF
  rw [show -(9 / 5 : ℝ) = -(9 : ℝ) / 5 by ring]
  ring

theorem upperNativeRatio_deriv (u : ℝ) : HasDerivAt upperNativeRatio (upperNativeRatioD u) u := by
  have h := (((hasDerivAt_id u).pow 2).const_mul (2304 / 8575)).const_add (5 / 7)
  convert h using 1
  · funext t
    simp only [upperNativeRatio, adjacentRatio, sub_self, mul_zero, add_zero, Pi.pow_apply, id_eq]
  · norm_num [upperNativeRatioD, id_eq] <;> ring

private theorem nativeL_deriv {u : ℝ} (hu : 0 < u) : HasDerivAt nativeL (-(1 / u)) u := by
  simpa only [one_div, nativeL] using (Real.hasDerivAt_log hu.ne').neg

private theorem nativeT_deriv {u : ℝ} (hu : 0 < u) : HasDerivAt nativeT (1 / (1 + u)) u := by
  have h := (Real.hasDerivAt_log (by positivity : (1 + u : ℝ) ≠ 0)).comp u ((hasDerivAt_id u).const_add 1)
  simpa only [nativeT, Function.comp_apply, mul_one, id_eq, one_div] using h

theorem nativeA_deriv {u : ℝ} (hu : 0 < u) : HasDerivAt nativeA (nativeAD u) u := by
  have h := hasDerivAt_id u
  have hA := ((h.const_mul (6 / 25)).mul (h.const_sub 2)).div (h.const_add 1) (by positivity)
  convert hA using 1
  simp only [nativeAD, id_eq, Pi.mul_apply]
  ring

private theorem upperNativeQ_deriv {u : ℝ} (hu : 0 < u) : HasDerivAt upperNativeQ (upperNativeQD u) u := by
  convert (upperNativeRatio_deriv u).mul (nativeL_deriv hu) using 1
  unfold upperNativeQD
  ring

private theorem upperNativeH_deriv {u : ℝ} (hu : 0 < u) : HasDerivAt upperNativeH (upperNativeHD u) u := by
  have hS := ((hasDerivAt_id u).const_mul (6 / 25)).const_add (13 / 25)
  have hY := (hS.const_mul (9 / 5)).sub_const 1
  have hQ := upperNativeQ_deriv hu
  have hL := nativeL_deriv hu
  convert (hS.mul ((hQ.const_mul 2).sub_const (3 / 10))).add
    ((hY.mul hL).mul (hQ.sub_const (3 / 10))) using 1
  simp only [upperNativeHD, nativeS, upperNativeY, id_eq, Pi.mul_apply]
  ring

private theorem upperNativeE_deriv {u : ℝ} (hu : 0 < u) : HasDerivAt upperNativeE (upperNativeED u) u := by
  have hA := nativeA_deriv hu
  have hT := nativeT_deriv hu
  convert (((hA.const_mul (9 / 5)).const_add 1).mul (hT.pow 2)).sub
    ((hA.const_mul 2).mul hT) using 1
  norm_num [upperNativeED, Pi.pow_apply] <;> ring

private theorem upperNativeF_deriv {u : ℝ} (hu : 0 < u) : HasDerivAt upperNativeF (upperNativeFD u) u := by
  have hA := nativeA_deriv hu
  have hT := nativeT_deriv hu
  convert (((hA.const_mul (9 / 5)).const_add 1).mul hT).sub hA using 1
  unfold upperNativeFD
  ring

theorem upperNativeUnshifted_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt upperNativeUnshifted (upperNativeUnshiftedD u) u := by
  have hP := Real.hasDerivAt_rpow_const (p := -(9 : ℝ) / 5) (Or.inl hu.ne')
  convert hP.mul (upperNativeH_deriv hu) using 1
  rw [upperNativeUnshiftedD, Real.rpow_sub_one hu.ne']
  ring

theorem upperNativeShifted_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt upperNativeShifted (upperNativeShiftedD u) u := by
  have hU : 0 < 1 + u := by positivity
  have hP := ((hasDerivAt_id u).const_add 1).rpow_const (p := -(9 : ℝ) / 5) (Or.inl hU.ne')
  have hS := ((upperNativeRatio_deriv u).mul (upperNativeE_deriv hu)).add
    ((upperNativeF_deriv hu).const_mul (3 / 10))
  convert hP.mul hS using 1
  simp only [upperNativeShiftedD, id_eq, one_mul, Pi.add_apply, Pi.mul_apply]
  rw [Real.rpow_sub_one hU.ne']
  ring

end ACS12.GammaMeasure
