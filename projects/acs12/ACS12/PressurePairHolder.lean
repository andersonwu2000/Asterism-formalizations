import ACS12.PressurePairLaw

/-! The complete angular tangent and original directed Hölder pressure. -/
namespace ACS12.Pressure

open Set

private theorem sin_tangent {x y : ℝ} (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    Real.sin y ≤ Real.sin x + (y - x) * Real.cos x := by
  have hMV {a b : ℝ} (hab : a < b) :
      ∃ c ∈ Ioo a b, Real.cos c = (Real.sin b - Real.sin a) / (b - a) := by
    obtain ⟨c,hc,h⟩ := exists_deriv_eq_slope Real.sin hab Real.continuous_sin.continuousOn
      Real.differentiable_sin.differentiableOn
    exact ⟨c,hc,(Real.hasDerivAt_sin c).deriv.symm.trans h⟩
  rcases lt_trichotomy x y with h | rfl | h
  · obtain ⟨c,hc,hC⟩ := hMV h
    have hC₀ : c ∈ Icc 0 Real.pi := ⟨hx.1.le.trans hc.1.le,hc.2.le.trans hy.2.le⟩
    have hB := Real.antitoneOn_cos (Ioo_subset_Icc_self hx) hC₀ hc.1.le
    rw [hC] at hB
    have h' := (div_le_iff₀ (sub_pos.mpr h)).mp hB
    linarith only [h']
  · simp
  · obtain ⟨c,hc,hC⟩ := hMV h
    have hC₀ : c ∈ Icc 0 Real.pi := ⟨hy.1.le.trans hc.1.le,hc.2.le.trans hx.2.le⟩
    have hB := Real.antitoneOn_cos hC₀ (Ioo_subset_Icc_self hx) hc.2.le
    rw [hC] at hB
    have h' := (le_div_iff₀ (sub_pos.mpr h)).mp hB
    linarith only [h']

noncomputable def pairTangent {n : ℕ} (θ φ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  1 + (halfArc φ i j - halfArc θ i j) * angularKernel 0 (halfArc θ i j)

theorem pairTangent_bound {n : ℕ} {θ φ : Fin n → ℝ} {i j : Fin n}
    (hθ : halfArc θ i j ∈ Ioo 0 Real.pi) (hφ : halfArc φ i j ∈ Ioo 0 Real.pi) :
    Real.sin (halfArc φ i j) / Real.sin (halfArc θ i j) ≤ pairTangent θ φ i j := by
  have hX := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  unfold pairTangent angularKernel
  rw [zero_add,Real.rpow_one]
  apply (div_le_iff₀ hX).mpr
  have h := sin_tangent hθ hφ
  have hE : (1 + (halfArc φ i j - halfArc θ i j) *
      (Real.cos (halfArc θ i j) / Real.sin (halfArc θ i j))) * Real.sin (halfArc θ i j) =
      Real.sin (halfArc θ i j) + (halfArc φ i j - halfArc θ i j) * Real.cos (halfArc θ i j) := by
    field_simp [hX.ne']
  exact h.trans_eq hE.symm

theorem pairTangent_pos {n : ℕ} {θ φ : Fin n → ℝ}
    (hθ : ∀ i j, j ≠ i → halfArc θ i j ∈ Ioo 0 Real.pi)
    (hφ : ∀ i j, j ≠ i → halfArc φ i j ∈ Ioo 0 Real.pi) (i j : Fin n) :
    0 < pairTangent θ φ i j := by
  by_cases h : j = i
  · subst j; simp only [pairTangent,halfArc_self,sub_self,zero_mul,add_zero,zero_lt_one]
  exact (div_pos (Real.sin_pos_of_pos_of_lt_pi (hφ i j h).1 (hφ i j h).2)
    (Real.sin_pos_of_pos_of_lt_pi (hθ i j h).1 (hθ i j h).2)).trans_le
      (pairTangent_bound (hθ i j h) (hφ i j h))

theorem originalPair_tangent_mean {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n)
    (F : Configuration n p) (φ : Fin n → ℝ) :
    (∑ i, ∑ j, originalPairLaw F i j * pairTangent (sortedPressureAngle F) φ i j) = 1 := by
  let θ := sortedPressureAngle F
  let m := sortedPressureMass F
  let C := originalPressureRow F
  let Δ (i : Fin n) := φ i - θ i
  have hWork := torque_work_zero hp m θ Δ (sortedPressure_torque hp F)
  have hPair (i j : Fin n) : originalPairLaw F i j * pairTangent θ φ i j =
      originalPairLaw F i j + (m i * m j * angularKernel p (halfArc θ i j) * (Δ j - Δ i)) /
        (2 * (massTotal m * C)) := by
    by_cases h : j = i
    · subst j
      simp only [pairTangent,halfArc_self,sub_self,zero_mul,add_zero,mul_one,mul_zero,zero_div]
    have ht := sortedPressureAngle_mem F h
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hK : angularCost p (halfArc θ i j) * angularKernel 0 (halfArc θ i j) =
        angularKernel p (halfArc θ i j) := by
      rw [angularCost,angularKernel,angularKernel,zero_add,Real.rpow_one,
        Real.rpow_add hs,Real.rpow_one]
      ring
    have hD : halfArc φ i j - halfArc θ i j = (Δ j - Δ i) / 2 := by
      unfold halfArc Δ
      ring
    unfold pairTangent
    rw [hD,← hK]
    change pairLaw p C m θ i j * _ = pairLaw p C m θ i j + _
    unfold pairLaw
    ring
  change (∑ i, ∑ j, originalPairLaw F i j * pairTangent θ φ i j) = 1
  simp only [hPair,Finset.sum_add_distrib,← Finset.sum_div,(originalPairLaw_marginals hp hn F).2.1,
    massWeight_sum_one (show 0 < n by omega) (show ∀ i, 0 < sortedPressureMass F i from fun i => F.mass_pos _)]
  change 1 + (∑ i, ∑ j, m i * m j * angularKernel p (halfArc θ i j) * (Δ j - Δ i)) /
    (2 * (massTotal m * C)) = 1
  rw [hWork,zero_div,add_zero]

/-- Original-source Hölder with the same sine tangent and the exact radial pair law. -/
theorem originalPair_holder {n : ℕ} {p : ℝ} (hp : 0 < p) (hn : 2 ≤ n)
    (F : Configuration n p) (v φ : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (hφ : ∀ i j, j ≠ i → halfArc φ i j ∈ Ioo 0 Real.pi) :
    let m := sortedPressureMass F
    let Q := ∑ i, ∑ j, originalPairLaw F i j * ((v i / m i) * (v j / m j)) ^ (1 / (p + 1))
    massTotal m * originalPressureRow F * Q ^ (p + 1) ≤ angularEnergy p v φ := by
  dsimp only
  let θ := sortedPressureAngle F
  let m := sortedPressureMass F
  let C := originalPressureRow F
  let πij := originalPairLaw F
  let u := pairTangent θ φ
  let R (i j : Fin n) := (v i / m i) * (v j / m j)
  let a : ℝ := 1 / (p + 1)
  have hm (i : Fin n) : 0 < m i := F.mass_pos _
  have hC : 0 < C := originalPressureRow_pos hn F
  have hM : 0 < massTotal m := massTotal_pos (by omega) hm
  have hPi := (originalPairLaw_marginals hp hn F).1
  have hU (i j : Fin n) : 0 < u i j := pairTangent_pos (fun i j h => sortedPressureAngle_mem F h) hφ i j
  have hR (i j : Fin n) : 0 < R i j := mul_pos (div_pos (hv i) (hm i)) (div_pos (hv j) (hm j))
  let w (k : Fin n × Fin n) := πij k.1 k.2 * u k.1 k.2
  let f (k : Fin n × Fin n) := R k.1 k.2 ^ a / u k.1 k.2
  have hW : ∑ k, w k = 1 := by
    simpa only [Fintype.sum_prod_type,w,u,πij,θ] using originalPair_tangent_mean hp hn F φ
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ w f
    (fun k _ => mul_nonneg (hPi k.1 k.2) (hU k.1 k.2).le) hW
    (fun k _ => (div_pos (Real.rpow_pos_of_pos (hR k.1 k.2) _) (hU k.1 k.2)).le)
    (p := p + 1) (by linarith only [hp])
  have hV (i j : Fin n) : w (i,j) * f (i,j) = πij i j * R i j ^ a := by
    dsimp only [w,f]
    field_simp [(hU i j).ne']
  have hV' (i j : Fin n) : w (i,j) * f (i,j) ^ (p + 1) =
      πij i j * R i j / u i j ^ p := by
    dsimp only [w,f]
    rw [Real.div_rpow (Real.rpow_nonneg (hR i j).le _) (hU i j).le,
      ← Real.rpow_mul (hR i j).le,show a * (p + 1) = 1 by unfold a; field_simp,
      Real.rpow_one,Real.rpow_add (hU i j) p 1,Real.rpow_one]
    field_simp [(hU i j).ne',(Real.rpow_pos_of_pos (hU i j) p).ne']
  simp only [Fintype.sum_prod_type,hV,hV'] at hJ
  change massTotal m * C * (∑ i, ∑ j, πij i j * R i j ^ a) ^ (p + 1) ≤ angularEnergy p v φ
  have hBound (i j : Fin n) : massTotal m * C * (πij i j * R i j / u i j ^ p) ≤
      v i * v j * angularCost p (halfArc φ i j) := by
    by_cases hij : j = i
    · subst j
      simp only [πij,originalPairLaw,pairLaw_diag hp,zero_mul,zero_div,halfArc_self,angularCost,
        Real.sin_zero,Real.zero_rpow hp.ne',div_zero,mul_zero,le_rfl]
    have hθ := sortedPressureAngle_mem F hij
    have ht := hφ i j hij
    have hθ₀ : 0 < Real.sin (halfArc θ i j) := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have ht₀ := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have h := (div_le_iff₀ hθ₀).mp (pairTangent_bound hθ ht)
    have hPow := Real.rpow_le_rpow ht₀.le h hp.le
    rw [Real.mul_rpow (hU i j).le hθ₀.le] at hPow
    have hCost := div_le_div_of_nonneg_left (mul_pos (hv i) (hv j)).le
      (Real.rpow_pos_of_pos ht₀ p) hPow
    have hEq : massTotal m * C * (πij i j * R i j / u i j ^ p) =
        (v i * v j) / (u i j ^ p * Real.sin (halfArc θ i j) ^ p) := by
      change massTotal m * C * ((m i * m j * (1 / Real.sin (halfArc θ i j) ^ p) /
        (massTotal m * C)) * ((v i / m i) * (v j / m j)) / u i j ^ p) =
          (v i * v j) / (u i j ^ p * Real.sin (halfArc θ i j) ^ p)
      field_simp [hM.ne',hC.ne',(hm i).ne',(hm j).ne',(Real.rpow_pos_of_pos hθ₀ p).ne',
        (Real.rpow_pos_of_pos (hU i j) p).ne']
    rw [hEq,angularCost]
    simpa only [div_eq_mul_inv,one_mul] using hCost
  refine (mul_le_mul_of_nonneg_left hJ (mul_pos hM hC).le).trans ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum fun j _ => hBound i j)

end ACS12.Pressure

