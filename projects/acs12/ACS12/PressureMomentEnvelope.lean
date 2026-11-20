import ACS12.PressureTestedImage
import ACS12.PureZetaBound

/-! The actual Laplace price of the opposite occupied edge. -/
namespace ACS12.Pressure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaMeasure
open scoped Topology

noncomputable def pressureNeighbor (p u y : ℝ) : ℝ :=
  2 * y + (1 + u) ^ (-p) *
    (1 + u ^ 3 * y / (1 + u) + (u ^ 3 * y / (1 + u)) ^ 2 / 2)

private noncomputable def momentShape (p η v : ℝ) : ℝ :=
  (1 + v) ^ (-p) * (1 + η * v / (1 + v) + (η * v / (1 + v)) ^ 2 / 2)

private theorem momentShape_convex {p η : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) : ConvexOn ℝ (Ici 0) (momentShape p η) := by
  let A := 1 + η + η ^ 2 / 2
  let B := η + η ^ 2
  let C := η ^ 2 / 2
  let f (v : ℝ) := A * (1 + v) ^ (-p) - B * (1 + v) ^ (-p - 1) + C * (1 + v) ^ (-p - 2)
  let f₁ (v : ℝ) := (-p * A) * (1 + v) ^ (-p - 1) -
    ((-p - 1) * B) * (1 + v) ^ (-p - 2) + ((-p - 2) * C) * (1 + v) ^ (-p - 3)
  let f₂ (v : ℝ) := p * (p + 1) * A * (1 + v) ^ (-p - 2) -
    (p + 1) * (p + 2) * B * (1 + v) ^ (-p - 3) +
    (p + 2) * (p + 3) * C * (1 + v) ^ (-p - 4)
  have hDer (q v : ℝ) (hv : -1 < v) :
      HasDerivAt (fun x => (1 + x) ^ q) (q * (1 + v) ^ (q - 1)) v := by
    have h := (Real.hasDerivAt_rpow_const (p := q)
      (Or.inl (show (1 + v : ℝ) ≠ 0 by linarith only [hv]))).comp v ((hasDerivAt_id v).const_add 1)
    simpa only [Function.comp_def,id_eq,mul_one] using h
  have h₁ (v : ℝ) (hv : -1 < v) : HasDerivAt f (f₁ v) v := by
    convert (((hDer (-p) v hv).const_mul A).sub ((hDer (-p - 1) v hv).const_mul B)).add
      ((hDer (-p - 2) v hv).const_mul C) using 1
    dsimp only [f₁]
    rw [show -p - 1 - 1 = -p - 2 by ring,show -p - 2 - 1 = -p - 3 by ring]
    ring
  have h₂ (v : ℝ) (hv : -1 < v) : HasDerivAt f₁ (f₂ v) v := by
    convert (((hDer (-p - 1) v hv).const_mul (-p * A)).sub
      ((hDer (-p - 2) v hv).const_mul ((-p - 1) * B))).add
      ((hDer (-p - 3) v hv).const_mul ((-p - 2) * C)) using 1
    dsimp only [f₂]
    rw [show -p - 1 - 1 = -p - 2 by ring,show -p - 2 - 1 = -p - 3 by ring,
      show -p - 3 - 1 = -p - 4 by ring]
    ring
  have hE (v : ℝ) (hv : 0 ≤ v) : f v = momentShape p η v := by
    have hT : 0 < 1 + v := by positivity
    have hR (k : ℕ) : (1 + v) ^ (-p - (k : ℝ)) = (1 + v) ^ (-p) / (1 + v) ^ k := by
      rw [Real.rpow_sub hT,Real.rpow_natCast]
    dsimp only [f,A,B,C,momentShape]
    have hR₁ := hR 1
    have hR₂ := hR 2
    norm_num only [Nat.cast_one,Nat.cast_ofNat,pow_one] at hR₁ hR₂
    rw [hR₁,hR₂]
    field_simp [hT.ne']
    ring
  have hPos (v : ℝ) (hv : 0 ≤ v) : 0 ≤ f₂ v := by
    let T := 1 + v
    have hT : 0 < T := by dsimp only [T]; positivity
    have hR (q : ℝ) (k : ℕ) (h : q = -p - 4 + (k : ℝ)) :
        T ^ q = T ^ (-p - 4) * T ^ k := by
      rw [h,Real.rpow_add hT,Real.rpow_natCast]
    have hE' : f₂ v = T ^ (-p - 4) *
        (p * (p + 1) * A * T ^ 2 - (p + 1) * (p + 2) * B * T + (p + 2) * (p + 3) * C) := by
      change p * (p + 1) * A * T ^ (-p - 2) - (p + 1) * (p + 2) * B * T ^ (-p - 3) +
        (p + 2) * (p + 3) * C * T ^ (-p - 4) = _
      rw [hR (-p - 2) 2 (by norm_num; ring),hR (-p - 3) 1 (by norm_num; ring),pow_one]
      ring
    rw [hE']
    apply mul_nonneg (Real.rpow_nonneg hT.le _)
    have hp₀ : 0 ≤ p := by linarith only [hp]
    have hη₂ : η ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hη hη₁ 2
    have hP₁ : 0 ≤ p * (p + 1) * A - (p + 1) * (p + 2) * B + (p + 2) * (p + 3) * C := by
      have hA : 0 ≤ (p - 9 / 5) * (p + 4 / 5) := mul_nonneg (sub_nonneg.mpr hp) (by positivity)
      have hB := mul_nonneg (show 0 ≤ 2 * p by positivity) (sub_nonneg.mpr hη₁)
      dsimp only [A,B,C]
      nlinarith only [hA,hB,sq_nonneg (η - 1),sq_nonneg η]
    have hSl : 0 ≤ 2 * p * A - (p + 2) * B := by
      have h := mul_nonneg (sub_nonneg.mpr (show p ≤ 2 by exact hp₂)) hη
      have h' := mul_nonneg (sub_nonneg.mpr hp₂) (sub_nonneg.mpr hη₁)
      dsimp only [A,B]
      nlinarith only [h',hη₂,hp]
    have hA : 0 ≤ p * (p + 1) * A * v ^ 2 := by dsimp only [A]; positivity
    have hB := mul_nonneg (mul_nonneg (show 0 ≤ p + 1 by positivity) hSl) hv
    dsimp only [T]
    nlinarith only [hP₁,hA,hB]
  have hConv : ConvexOn ℝ (Ici 0) f := by
    apply convexOn_of_deriv2_nonneg (convex_Ici 0)
    · intro v hv
      exact (h₁ v (by have : 0 ≤ v := hv; linarith)).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Ici,mem_Ioi] at hv
      exact (h₁ v (by linarith)).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici,mem_Ioi] at hv
      have hEq : deriv f =ᶠ[𝓝 v] f₁ := by
        filter_upwards [Ioi_mem_nhds (show -1 < v by linarith)] with x hx
        exact (h₁ x hx).deriv
      exact ((h₂ v (by linarith)).congr_of_eventuallyEq hEq).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici,mem_Ioi] at hv
      have hEq : deriv f =ᶠ[𝓝 v] f₁ := by
        filter_upwards [Ioi_mem_nhds (show -1 < v by linarith)] with x hx
        exact (h₁ x hx).deriv
      change 0 ≤ deriv (deriv f) v
      rw [hEq.deriv_eq,(h₂ v (by linarith)).deriv]
      exact hPos v hv.le
  exact hConv.congr (fun v hv => hE v hv)

theorem pressureNeighbor_mono {p u y z : ℝ} (hu : 1 ≤ u) (hy : 0 ≤ y) (hyz : y ≤ z) :
    pressureNeighbor p u y ≤ pressureNeighbor p u z := by
  unfold pressureNeighbor
  have hu₀ : 0 ≤ u := zero_le_one.trans hu
  gcongr <;> positivity

theorem pressureNeighbor_anti {p q u y : ℝ} (hu : 1 ≤ u) (hy : 0 ≤ y) (hpq : p ≤ q) :
    pressureNeighbor q u y ≤ pressureNeighbor p u y := by
  have hu₀ : 0 ≤ u := zero_le_one.trans hu
  unfold pressureNeighbor
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by linarith only [hu]) (neg_le_neg hpq)) (by positivity)

private theorem atomMoment_ratio {p η d z y u : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hu : 1 ≤ u) (hd : u ≤ d) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hz₁ : z ≤ 1) (hEq : η * d = u ^ 3 * y) :
    2 * y * z + momentShape p η (d * z) ≤ max 1 (pressureNeighbor p u y) := by
  have hp₀ : 0 ≤ p := by linarith only [hp]
  have hd₀ : 0 ≤ d := by linarith only [hu,hd]
  have hu₀ : 0 ≤ u := by linarith only [hu]
  have hB : momentShape p η d ≤
      (1 + u) ^ (-p) * (1 + u ^ 3 * y / (1 + u) + (u ^ 3 * y / (1 + u)) ^ 2 / 2) := by
    unfold momentShape
    rw [hEq]
    have hD := div_le_div_of_nonneg_left (show 0 ≤ u ^ 3 * y by positivity)
      (show 0 < 1 + u by positivity) (show 1 + u ≤ 1 + d by linarith only [hd])
    apply mul_le_mul
    · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hd]) (neg_nonpos.mpr hp₀)
    · gcongr <;> positivity
    · positivity
    · positivity
  have h := (momentShape_convex hp hp₂ hη hη₁).2 (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
    (show d ∈ Ici 0 from hd₀) (sub_nonneg.mpr hz₁) hz (by ring : 1 - z + z = 1)
  simp only [smul_eq_mul,mul_zero,zero_add,mul_comm z d] at h
  have hZero : momentShape p η 0 = 1 := by simp [momentShape]
  rw [hZero,mul_one] at h
  let K := max 1 (pressureNeighbor p u y)
  have hK₁ : 1 ≤ K := le_max_left _ _
  have hK₂ : 2 * y + momentShape p η d ≤ K := (add_le_add_right hB _).trans (le_max_right _ _)
  have hA := mul_le_mul_of_nonneg_left hK₁ (sub_nonneg.mpr hz₁)
  have hD := mul_le_mul_of_nonneg_left hK₂ hz
  change _ ≤ K
  linarith only [h,hA,hD]


private theorem minimumAtom_quadratic {a r g s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    minimumAtomTest a r g s ≤
      a * s + Real.exp (-s * g) * (1 + (r / 2) * s + (r ^ 2 / 12) * s ^ 2) := by
  have h := mul_lt_mul_of_pos_left (bose_inverse_B2 (mul_pos hs hr)) (mul_pos hs hr)
  have hInv := mul_inv_cancel₀ (mul_pos hs hr).ne'
  have hHead : (s * r) * (1 - Real.exp (-(s * r)))⁻¹ ≤ 1 + (r / 2) * s + (r ^ 2 / 12) * s ^ 2 := by
    nlinarith only [h,hInv]
  have hE : minimumAtomTest a r g s =
      a * s + Real.exp (-s * g) * ((s * r) * (1 - Real.exp (-(s * r)))⁻¹) := by
    unfold minimumAtomTest oppositeRayBose pressureBose periodicDen
    rw [show -s * g = -(g - r) * s + -s * r by ring,Real.exp_add,
      show -(s * r) = -s * r by ring]
    ring
  rw [hE]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hHead (Real.exp_pos _).le) _

private theorem testedImage_moment_le {p L a r g x : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ha : 0 ≤ a) (hr : 0 < r) (hg : r ≤ g) (hx : 0 < x) :
    testedImage p L (minimumAtomTest a r g) x ≤
      (2 * a / x) * imagePotential p L x +
      imagePotential p L (x + g) * (1 + r / (x + g) + (r / (x + g)) ^ 2 / 2) := by
  let k := imagePotential p L
  let U := imageSlope p L
  let w := GammaMeasure.imageDensity p L
  let t := x + g
  let M := sourceLaplaceMoment p L
  let f (s : ℝ) := w s * minimumAtomTest a r g s * Real.exp (-s * x)
  let b (v s : ℝ) := w s * Real.exp (-s * v)
  let b₁ (v s : ℝ) := w s * s * Real.exp (-s * v)
  let b₂ (s : ℝ) := w s * s ^ 2 * Real.exp (-s * t)
  let F (s : ℝ) := a * b₁ x s + b t s + (r / 2) * b₁ t s + (r ^ 2 / 12) * b₂ s
  have ht : 0 < t := add_pos hx (hr.trans_le hg)
  have hBI : IntegrableOn (b t) (Ioi 0) := imagePotential_integrable hp hL ht
  have hUI (v : ℝ) (hv : 0 < v) : IntegrableOn (b₁ v) (Ioi 0) := imageSlope_integrable hp hL hv
  have hM : IntegrableOn b₂ (Ioi 0) := sourceLaplaceMoment_integrable hp hL ht 2
  have hFI : IntegrableOn F (Ioi 0) :=
    ((((hUI x hx).const_mul a).add hBI).add ((hUI t ht).const_mul (r / 2))).add (hM.const_mul _)
  have hNonneg (s : ℝ) (hs : 0 < s) : 0 ≤ f s :=
    mul_nonneg (mul_nonneg (imageDensity_pos hp hL hs).le (minimumAtomTest_bounds ha hr hg hs).1)
      (Real.exp_pos _).le
  have hPoint (s : ℝ) (hs : 0 < s) : f s ≤ F s := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (minimumAtom_quadratic (a := a) (g := g) hr hs) (imageDensity_pos hp hL hs).le)
      (Real.exp_pos (-s * x)).le
    have hExp : Real.exp (-s * g) * Real.exp (-s * x) = Real.exp (-s * t) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [t]
      ring
    change f s ≤ _
    change f s ≤ w s * (a * s + Real.exp (-s * g) * _) * Real.exp (-s * x) at h
    convert h using 1
    dsimp only [F,b,b₁,b₂]
    rw [← hExp]
    ring
  have hfI : IntegrableOn f (Ioi 0) := by
    have hMeas : Measurable f := by
      unfold f minimumAtomTest oppositeRayBose pressureBose periodicDen
      exact ((continuous_imageDensity hp hL).measurable.mul (by fun_prop)).mul (by fun_prop)
    apply hFI.mono' hMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (hNonneg s hs)]
    exact hPoint s hs
  have hF : testedImage p L (minimumAtomTest a r g) x ≤
      a * U x + k t + (r / 2) * U t + (r ^ 2 / 12) * M 2 t := by
    have h := setIntegral_mono_on hfI hFI measurableSet_Ioi fun s hs => hPoint s hs
    unfold F at h
    rw [integral_add (f := fun s => a * b₁ x s + b t s + (r / 2) * b₁ t s)
        ((((hUI x hx).const_mul a).add hBI).add ((hUI t ht).const_mul _)) (hM.const_mul _),
      integral_add (f := fun s => a * b₁ x s + b t s)
        (((hUI x hx).const_mul a).add hBI) ((hUI t ht).const_mul _),
      integral_add ((hUI x hx).const_mul a) hBI,integral_const_mul,integral_const_mul,integral_const_mul] at h
    exact h
  have h₂ := pressureLaplaceMoment_upper hp hp₂ hL ht 1
  norm_num only [Nat.cast_one,Nat.reduceAdd] at h₂
  simp only [sourceLaplaceMoment,pow_one] at h₂
  change t * M 2 t ≤ 3 * U t at h₂
  have hSx : U x ≤ 2 * k x / x := (le_div_iff₀ hx).mpr (by simpa only [mul_comm] using imageSlope_mul_le_double hp hp₂ hL hx)
  have hSt : U t ≤ 2 * k t / t := (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using imageSlope_mul_le_double hp hp₂ hL ht)
  have hMt : M 2 t ≤ 6 * k t / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    have h := mul_le_mul_of_nonneg_right h₂ ht.le
    have h' := mul_le_mul_of_nonneg_left (imageSlope_mul_le_double hp hp₂ hL ht) (by norm_num : (0 : ℝ) ≤ 3)
    change 3 * (t * U t) ≤ 3 * (2 * k t) at h'
    nlinarith only [h,h']
  have hX := mul_le_mul_of_nonneg_left hSx ha
  have hT := mul_le_mul_of_nonneg_left hSt (show 0 ≤ r / 2 by positivity)
  have hM' := mul_le_mul_of_nonneg_left hMt (show 0 ≤ r ^ 2 / 12 by positivity)
  change _ ≤ (2 * a / x) * k x + k t * (1 + r / t + (r / t) ^ 2 / 2)
  rw [div_pow]
  have hEq : a * (2 * k x / x) + k t + (r / 2) * (2 * k t / t) +
      (r ^ 2 / 12) * (6 * k t / t ^ 2) =
      (2 * a / x) * k x + k t * (1 + r / t + (r ^ 2 / t ^ 2) / 2) := by ring
  linarith only [hF,hX,hT,hM',hEq]

theorem minimumAtom_moment_le {p L a r g t x u : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ha : 0 ≤ a) (hr : 0 < r) (hg : r ≤ g)
    (ht : 0 < t) (htx : t ≤ x) (hu : 1 ≤ u) (hgu : t * u ≤ g) (hrE : r = u ^ 3 * a) :
    testedImage p L (minimumAtomTest a r g) x ≤
      max 1 (pressureNeighbor p u (a / t)) * imagePotential p L x := by
  let η := r / g
  let d := g / t
  let y := a / t
  let z := t / x
  let k := imagePotential p L
  have hx := ht.trans_le htx
  have hg₀ := hr.trans_le hg
  have hp₀ : 0 < p := by linarith only [hp]
  have hη := div_nonneg hr.le hg₀.le
  have hη₁ := (div_le_one hg₀).mpr hg
  have hd : u ≤ d := (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hgu)
  have hy := div_nonneg ha ht.le
  have hz := div_nonneg ht.le hx.le
  have hz₁ := (div_le_one hx).mpr htx
  have hEq : η * d = u ^ 3 * y := by
    unfold η d y
    field_simp [hg₀.ne',ht.ne']
    rw [hrE]
  have hCh := atomMoment_ratio hp hp₂ hη hη₁ hu hd hy hz hz₁ hEq
  have hM := testedImage_moment_le hp₀ hp₂ hL ha hr hg hx
  have hS := imagePotential_scaled_upper (by linarith only [hp] : 1 ≤ p) hp₂ hL hx
    (le_add_of_nonneg_right hg₀.le)
  have hF := mul_le_mul_of_nonneg_right hS
    (show 0 ≤ 1 + r / (x + g) + (r / (x + g)) ^ 2 / 2 by positivity)
  have h1 : 2 * y * z = 2 * a / x := by unfold y z; field_simp [ht.ne',hx.ne']
  have h2 : (1 + d * z) ^ (-p) = (x / (x + g)) ^ p := by
    have hE : 1 + d * z = (x + g) / x := by unfold d z; field_simp [ht.ne',hx.ne']
    rw [hE,Real.rpow_neg (by positivity),← Real.inv_rpow (by positivity),inv_div]
  have h3 : η * (d * z) / (1 + d * z) = r / (x + g) := by
    unfold η d z
    field_simp [ht.ne',hx.ne',hg₀.ne',(add_pos hx hg₀).ne']
  rw [h1,momentShape,h2,h3] at hCh
  have hFin := mul_le_mul_of_nonneg_right hCh (imagePotential_pos hp₀ hL hx).le
  exact hM.trans (by linarith only [hF,hFin])

end ACS12.Pressure

