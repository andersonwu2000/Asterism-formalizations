import ACS12.FourthRoot

/-! Exact pointwise comparisons of the original fourth-source partials. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set

noncomputable def fourthFirstStream (u s : ℝ) : ℝ :=
  Real.exp (-s * u) * (u + scaledExpTail s 1)

noncomputable def fourthV (u v r m s : ℝ) : ℝ :=
  s * (1 - Real.exp (-s * v)) * fourthFirstStream u s +
    Real.exp (-s * v) * (v * s * expHeadFactor (r * s) - m * s)

noncomputable def fourthD (v r s : ℝ) : ℝ :=
  Real.exp (-s * v) * (1 + v * s) + polyA (v * s) * BoseShape.C (r * s)

theorem fourthD_pos {v r s : ℝ} (hv : 0 < v) (hr : 0 < r) (hs : 0 < s) :
    0 < fourthD v r s := by
  unfold fourthD
  exact add_pos (mul_pos (Real.exp_pos _) (by positivity))
    (mul_pos (polyA_pos (mul_pos hv hs)) (BoseShape.C_pos (mul_pos hr hs)))

theorem fourthV_pos {u v r m s : ℝ} (hu : 0 < u) (hv : 0 < v) (hr : 0 < r)
    (hs : 0 < s) (hmv : m ≤ v) : 0 < fourthV u v r m s := by
  have hHead : 1 < expHeadFactor (r * s) :=
    (lt_add_of_pos_right _ (div_pos (mul_pos hr hs) (by norm_num : (0 : ℝ) < 2))).trans
      (BoseShape.expHeadFactor_gt_one_add_half (mul_pos hr hs))
  have hTerm : 0 < v * s * expHeadFactor (r * s) - m * s := by
    have h := mul_lt_mul_of_pos_left hHead (mul_pos hv hs)
    exact sub_pos.mpr ((mul_le_mul_of_nonneg_right hmv hs.le).trans_lt (by simpa only [mul_one] using h))
  have hS : 0 < fourthFirstStream u s := mul_pos (Real.exp_pos _) (add_pos hu
    (div_pos zero_lt_one (expTail_den_pos (by simpa only [mul_one] using hs))))
  unfold fourthV
  have he : 0 < 1 - Real.exp (-s * v) := by
    simpa only [neg_mul] using expHead_den_pos (mul_pos hs hv)
  exact add_pos (mul_pos (mul_pos hs he) hS) (mul_pos (Real.exp_pos _) hTerm)

private theorem fourthFirstStream_lt_beta {u v s : ℝ} (hv : 0 < v) (hvu : v ≤ u)
    (hu₁ : u < 1) (hs : 0 < s) : fourthFirstStream u s < scaledExpTail s v := by
  have hu := hv.trans_le hvu
  unfold fourthFirstStream
  calc
    _ < Real.exp (-s * u) * (u + scaledExpTail s u) :=
      mul_lt_mul_of_pos_left (add_lt_add_right (scaledExpTail_strictAnti hs hu (mem_Ioi.mpr zero_lt_one) hu₁) _)
        (Real.exp_pos _)
    _ = scaledExpTail s u := scaledExpTail_bridge hs hu
    _ ≤ _ := (scaledExpTail_strictAnti hs).antitoneOn hv hu hvu

private theorem fourthFirstTerm_lt {u v s : ℝ} (hv : 0 < v) (hvu : v ≤ u)
    (hu₁ : u < 1) (hs : 0 < s) :
    s * (1 - Real.exp (-s * v)) * fourthFirstStream u s <
      v * s * Real.exp (-s * v) := by
  have hDen : 0 < 1 - Real.exp (-s * v) := by
    simpa only [neg_mul] using expHead_den_pos (mul_pos hs hv)
  have hT := mul_lt_mul_of_pos_left (fourthFirstStream_lt_beta hv hvu hu₁ hs) (mul_pos hs hDen)
  have hE : s * (1 - Real.exp (-s * v)) * scaledExpTail s v = v * s * Real.exp (-s * v) := by
    linear_combination -s * scaledExpTail_bridge hs hv
  rwa [hE] at hT

theorem fourth_diagonal_speed_lt {u v r s : ℝ} (hv : 0 < v) (hvu : v ≤ u)
    (hu₁ : u < 1) (hr : 0 < r) (hrv : r ≤ v) (hs : 0 < s) :
    fourthV u v r v s + Real.exp (-s * v) - 2 * fourthD v r s <
      diagonalSpeedKernel (v * s) := by
  have hX : 0 < v * s := mul_pos hv hs
  have hY : 0 < r * s := mul_pos hr hs
  have hYX : r * s ≤ v * s := mul_le_mul_of_nonneg_right hrv hs.le
  have hHead := strictMonoOn_expHeadFactor.monotoneOn hY hX hYX
  have hC := BoseShape.C_antitone hY hX hYX
  have hD := mul_le_mul_of_nonneg_left hC (polyA_pos hX).le
  have hV := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHead hX.le) (Real.exp_pos (-s * v)).le
  have hT := fourthFirstTerm_lt hv hvu hu₁ hs
  simp only [fourthV, fourthD, diagonalSpeedKernel, show -(v * s) = -s * v by ring]
  nlinarith only [hD, hV, hT]

theorem fourth_fixed_speed_lt {u v r m s : ℝ} (hv : 0 < v) (hvu : v ≤ u)
    (hu₁ : u < 1) (hr : 0 < r) (hrv : r ≤ v) (hs : 0 < s) :
    fourthV u v r m s - 2 * fourthD v r s < fixedMassSpeedKernel (m / v) (v * s) := by
  have h := fourth_diagonal_speed_lt hv hvu hu₁ hr hrv hs
  have hV : fourthV u v r m s = fourthV u v r v s + Real.exp (-s * v) * ((v - m) * s) := by
    unfold fourthV
    ring
  have hm : (1 - m / v) * (v * s) = (v - m) * s := by field_simp [hv.ne']
  rw [hV, fixedMassSpeedKernel, hm, show -(v * s) = -s * v by ring]
  linarith only [h]

end ACS12.GammaMeasure

