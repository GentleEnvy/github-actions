import NavierStokesAB.SmallData.Cauchy

/-!
# Real parts of Fourier series, and their algebra

* `re3 : ℂ³ →L[ℝ] ℝ³` and `ofReal3 : ℝ³ →L[ℝ] ℂ³`;
* `four` is additive and commutes with bounded linear maps;
* Hermitian coefficients (`c (-k) = conj (c k)`) give real fields (`vconj_four`).
-/

open Real Complex Set Filter Topology MeasureTheory
open scoped NNReal BoundedContinuousFunction InnerProductSpace ComplexConjugate ContDiff

set_option synthInstance.maxHeartbeats 200000

namespace NavierStokesAB.SmallData

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ### Real parts -/

/-- Componentwise real part. -/
noncomputable def re3 : V →L[ℝ] ℝ³ :=
  LinearMap.mkContinuous
    { toFun := fun z => WithLp.toLp 2 fun i => (z i).re
      map_add' := fun z w => by ext i; simp
      map_smul' := fun r z => by ext i; simp }
    1 fun z => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [Real.norm_eq_abs, sq_abs]
      exact sq_le_sq' (neg_le_of_abs_le (Complex.abs_re_le_norm _))
        (le_of_abs_le (Complex.abs_re_le_norm _))

@[simp] theorem re3_apply (z : V) (i : Fin 3) : re3 z i = (z i).re := rfl

/-- Componentwise inclusion `ℝ³ → ℂ³`. -/
noncomputable def ofReal3 : ℝ³ →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := fun v => WithLp.toLp 2 fun i => ((v i : ℝ) : ℂ)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun r v => by ext i; simp }
    1 fun v => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      simp

@[simp] theorem ofReal3_apply (v : ℝ³) (i : Fin 3) : ofReal3 v i = (v i : ℂ) := rfl

theorem ofReal3_re3 {z : V} (hz : vconj z = z) : ofReal3 (re3 z) = z := by
  ext i
  have h := congrArg (fun w : V => w i) hz
  simp only [vconj_apply] at h
  simp only [ofReal3_apply, re3_apply]
  exact Complex.conj_eq_iff_re.1 h

theorem inner_kC_ofReal3 (k : Λ) (v : ℝ³) :
    ⟪kC k, ofReal3 v⟫_ℂ = ((⟪kR k, v⟫_ℝ : ℝ) : ℂ) := by
  rw [inner_kC, PiLp.inner_apply]
  push_cast
  simp [mul_comm]

theorem re_inner_ofReal3 (h : ℝ³) (z : V) : (⟪ofReal3 h, z⟫_ℂ).re = ⟪re3 z, h⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

/-! ### Algebra of Fourier series -/

section Algebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem RapidDecay.add {c c' : Λ → E} (hc : RapidDecay c) (hc' : RapidDecay c') :
    RapidDecay (c + c') := fun m =>
  ((hc m).add (hc' m)).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg (kn_nonneg k) m)

theorem RapidDecay.of_norm_le {c : Λ → E} {c' : Λ → F} (hc : RapidDecay c) {C : ℝ}
    (h : ∀ k, ‖c' k‖ ≤ C * ‖c k‖) : RapidDecay c' := fun m =>
  ((hc m).mul_left C).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (norm_nonneg _)) fun k => by
      calc kn k ^ m * ‖c' k‖ ≤ kn k ^ m * (C * ‖c k‖) :=
            mul_le_mul_of_nonneg_left (h k) (pow_nonneg (kn_nonneg k) m)
        _ = C * (kn k ^ m * ‖c k‖) := by ring

theorem four_add {c c' : Λ → E} (hc : RapidDecay c) (hc' : RapidDecay c') (x : ℝ³) :
    four (fun k => c k + c' k) x = four c x + four c' x := by
  unfold four
  rw [← (summable_four hc x).tsum_add (summable_four hc' x)]
  simp [smul_add]

theorem four_map (L : E →L[ℂ] F) {c : Λ → E} (hc : RapidDecay c) (x : ℝ³) :
    L (four c x) = four (fun k => L (c k)) x := by
  unfold four
  rw [L.map_tsum (summable_four hc x)]
  simp

theorem four_mapR (L : E →L[ℝ] F) {c : Λ → E} (hc : RapidDecay c) (x : ℝ³)
    (hL : ∀ (z : ℂ) (e : E), L (z • e) = z • L e) :
    L (four c x) = four (fun k => L (c k)) x := by
  unfold four
  rw [L.map_tsum (summable_four hc x)]
  simp [hL]

@[simp] theorem four_zero_coef (x : ℝ³) : four (fun _ : Λ => (0 : E)) x = 0 := by
  simp [four]

end Algebra

/-! ### Hermitian coefficients give real fields -/

theorem vconj_four {c : Λ → V} (hc : RapidDecay c) (hherm : ∀ k, c (-k) = vconj (c k))
    (x : ℝ³) : vconj (four c x) = four c x := by
  unfold four
  rw [← vconjL_apply, vconjL.map_tsum (summable_four hc x)]
  simp only [vconjL_apply, vconj_smul, conj_emode]
  have : ∀ k, emode (-k) x • vconj (c k) = emode (-k) x • c (-k) := fun k => by rw [hherm]
  simp only [this]
  exact (Equiv.neg Λ).tsum_eq (fun k => emode k x • c k)

end NavierStokesAB.SmallData
