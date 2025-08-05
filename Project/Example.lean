--min_import
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Choose.Cast

open scoped BigOperators

--theorem1 余りの積
theorem card (n : ℕ) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n := by
  cases n with
  | zero => exact (not_finite (ZMod 0)).elim
  | succ n => convert Fintype.card_fin (n + 1) using 2
  --

theorem card_units (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [Fintype.card_units, card]

/-
theorem katabami_theorem_fermat1 {a p : ℕ} (hp : p.Prime) (ha : a.Coprime p) : a ^ (p - 1) ≡ 1 [MOD p] := by
  -- a が単元であることを示す
  -- ZMod p を体として扱う
  haveI : Fact p.Prime := ⟨hp⟩
  --実際に単元であることを示す
  have unit_a : IsUnit (a : ZMod p) := by
    -- a ≠ 0 mod p
    have ha_ne_zero : (a : ZMod p) ≠ 0 := by
      intro h
      have mod_zero : a % p = 0 := by
        sorry

    -- 単元 u として a を取り出す
  obtain ⟨u, hu⟩ := unit_a

  -- 単元 u の (p - 1) 乗は単位元 1 になる
  have pow_eq_one : u ^ (p - 1) = 1 := sorry
-/

--theorem2 二項定理
open Nat

theorem Int.NatAbs_natCast_ori (n : Nat) : natAbs ↑n = n := rfl

theorem val_natCast (n a : ℕ) : (a : ZMod n).val = a % n := by
  cases n
  · rw [Nat.mod_zero]
    exact Int.NatAbs_natCast_ori a
  · apply Fin.val_natCast

theorem eq_iff_modEq_nat_fermat (n : ℕ) {a b : ℕ} : (a : ZMod n) = b ↔ a ≡ b [MOD n] := by
  cases n
  · simp [Nat.ModEq, Nat.mod_zero]
  · rw [Fin.ext_iff, Nat.ModEq, ← val_natCast, ← val_natCast]
    exact Iff.rfl

lemma dvd_choose (p a b : ℕ) (hp : p.Prime) (ha : a < p) (hab : b - a < p) (h : p ≤ b) : p ∣ choose b a :=
  have : a + (b - a) = b := Nat.add_sub_of_le (ha.le.trans h)
  this ▸ hp.dvd_choose_add ha hab (this.symm ▸ h)

  -- a = n (mod n) ↔ a | n
theorem nat_cast_eq_zero_iff_dvd {p n : ℕ} [hp : Fact p.Prime] :
    (n : ZMod p) = 0 ↔ p ∣ n := by
  constructor
  · intro h
    apply Nat.dvd_of_mod_eq_zero
    rw [← ZMod.val_eq_zero] at h
    have hn_def : (↑n : ZMod p).val = n % p := by
      apply ZMod.val_natCast
    rw [←hn_def]
    rw [h]
  · intro h
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    obtain ⟨k, rfl⟩ := h
    rw [← ZMod.val_eq_zero]
    rw [ZMod.val_natCast]
    exact Nat.mul_mod_right p k

--帰納法の準備として、(a + 1) ^ p ≡ ↑a ^ p + 1を示しておく
theorem fermat2_pre {a p : ℕ} (hp : p.Prime) : (a + 1) ^ p ≡ ↑a ^ p + 1 [MOD p] := by
  -- 1 ≤ k ≤ p−1 の範囲で中間項が 0 になることを示す
  let terms := Finset.Ico 1 p
  have h_middle : ∑ k ∈ terms, (p.choose k : ZMod p) * (a : ZMod p) ^ k = 0:= by
    apply Finset.sum_eq_zero
    intro h hk
    have h_pos : 0 < h := Nat.lt_of_lt_of_le (by norm_num) (Finset.mem_Ico.mp hk).1
    have p_pos : 0 < p := hp.pos
    have h1 : h ≠ 0 := Nat.ne_of_gt h_pos
    have h2 : h < p := (Finset.mem_Ico.mp hk).2
    -- p.choose h = 0を証明
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have p_neg_h_pos_p : p - h < p := by exact Nat.sub_lt p_pos h_pos
    have p_eq_pos_p : p ≤ p := by rfl
    have dvd_p_choose : p ∣ choose p h := by
      apply dvd_choose p h p hp h2 p_neg_h_pos_p p_eq_pos_p
    have p_choose_zero : (↑(p.choose h) : ZMod p) = 0 := by
      exact (nat_cast_eq_zero_iff_dvd.mpr dvd_p_choose)
    calc
      (↑(p.choose h) : ZMod p) * (↑a : ZMod p) ^ h
          = 0 * (↑a : ZMod p) ^ h := by rw [p_choose_zero]
      _ = 0 := by rw [zero_mul]
  --ここまで中間項の計算

  --和の分離の計算
  have sum_split : ∑ x ∈ Finset.range p, ↑(p.choose x) * (a : ZMod p) ^ x
    = ↑(p.choose 0) * (a : ZMod p)^0 + ∑ x ∈ terms, ↑(p.choose x) * (a : ZMod p) ^ x := by
        have range_eq : Finset.range p = insert 0 (Finset.Ico 1 p) := by
          rw [Finset.range_eq_Ico]
          have : Finset.Ico 0 p = insert 0 (Finset.Ico 1 p) := by
            apply Finset.ext
            intro x
            simp only [Finset.mem_Ico, Finset.mem_insert]
            constructor
            · intro ⟨h₁, h₂⟩
              by_cases hx0 : x = 0
              · left; exact hx0
              · right; exact ⟨Nat.pos_of_ne_zero hx0, h₂⟩
            · intro h
              cases h with
              | inl h0 => rw [h0]; exact ⟨Nat.zero_le _, hp.pos⟩
              | inr rw =>
                let ⟨h₁, h₂⟩ := rw
                exact ⟨Nat.zero_le x, h₂⟩
          exact this
        rw [range_eq]
        simp
        dsimp [terms]

  -- (a + 1) ^ p ≡ a + 1 [MOD p] を二項展開によって導く(a ^ p ≡ a [MOD p])

  calc
    -- 二項展開 (a + 1) ^ p の形で表現
    (a + 1) ^ p
      = ∑ k ∈ Finset.range (p + 1), p.choose k * a ^ k * 1 ^ (p - k) := by
        --1 ^ (p - k)を消去しつつΣを展開
        simp [add_pow, mul_comm]
    -- 和の端点 k=0, k=p の項を明示的に計算する
    _ ≡ ∑ x ∈ Finset.range p, ↑(p.choose x) * ↑a ^ x + ↑a ^ p [MOD p]:= by
      rw [Finset.sum_range_succ]
      simp [Nat.cast_choose, Nat.cast_pow, Nat.cast_mul, Nat.cast_one]
      ring_nf at h_middle
      rfl
    _ ≡ ↑(p.choose 0) * ↑a ^ 0 + ∑ x ∈ terms, ↑(p.choose x) * ↑a ^ x + ↑a ^ p [MOD p]:= by
      rw [← eq_iff_modEq_nat_fermat]
      norm_num
      rw [sum_split]
      norm_num
    _ ≡ ↑a ^ p + 1 [MOD p]:= by
      simp only [Nat.choose_zero_right, pow_zero, Nat.cast_one]
      rw [← eq_iff_modEq_nat_fermat]
      simp
      rw [h_middle]
      simp
      rw [add_comm]

--帰納法を使うため、一度N上の命題として解く
theorem fermat_binomial_theorem (p: ℕ) (hp : Nat.Prime p) :
  ∀ n : ℕ, (n + 1) ^ p ≡ n + 1 [MOD p] := by
  intro n
  induction n with
  | zero =>
    ring_nf
    rfl
  | succ n ih =>
    have h := fermat2_pre hp (a := n + 1)
    exact Nat.ModEq.trans h (Nat.ModEq.add_right _ ih)

/-
この時点でフェルマーの小定理としては解けている
((n + 1) ^ p ≡ n + 1 [MOD p], n ∈ ℕ(0含む) から a^p ≡ a [MOD p]の形に解いたことになる)
-/

theorem Nat.not_dvd_one {a : ℕ} (h : a ≠ 1) : ¬ a ∣ 1 := by
  intro h'
  have hle : a ≤ 1 := Nat.le_of_dvd (by decide) h'
  interval_cases a <;> simp_all

theorem Nat.coprime_not_dvd {a b : ℕ} (h : a.Coprime b) (hne : a ≠ 1) : ¬ a ∣ b := by
  intro h'
  have d : a ∣ Nat.gcd a b := Nat.dvd_gcd (Nat.dvd_refl a) h'
  rw [h.gcd_eq_one] at d
  rw [Nat.dvd_one] at d
  exact hne d

--右辺をもとの形式に変える
theorem fermat_via_binomial (p n : ℕ) (hp : Nat.Prime p) (hcoprime : Nat.Coprime (n + 1) p) :
  (n + 1) ^ (p - 1) ≡ 1 [MOD p] := by
  have h := fermat_binomial_theorem p hp n
  rw [← eq_iff_modEq_nat_fermat]
  rw [← eq_iff_modEq_nat_fermat] at h
  have n_mul: ↑((n + 1) ^ p) = ↑(n + 1) * ↑((n + 1) ^ (p - 1)) := by
    rw [← Nat.sub_add_cancel (Nat.Prime.pos hp)]
    rw [Nat.pow_succ]
    ring_nf
    simp
  rw [n_mul] at h
  rw [mul_comm] at h
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have inv : (↑(n + 1) : ZMod p)⁻¹ * ↑((n + 1) ^ (p - 1) * (n + 1)) = (↑(n + 1) : ZMod p)⁻¹ * ↑(n + 1) := by
    rw [h]
  have a_ne_zero : (↑(n + 1) : ZMod p) ≠ 0 := by
    intro h_zero
    rw [nat_cast_eq_zero_iff_dvd] at h_zero
    have : Nat.Coprime p (n + 1) := hcoprime.symm
    have hne : n + 1 ≠ 1 := by
      intro h_eq
      rw [← nat_cast_eq_zero_iff_dvd] at h_zero
      have h_dvd : p ∣ n + 1 := by
        rw [nat_cast_eq_zero_iff_dvd] at h_zero
        exact h_zero
      exact Nat.coprime_not_dvd hcoprime.symm (Nat.Prime.ne_one hp) h_dvd
    have h_dvd : p ∣ n + 1 := by
      rw [← nat_cast_eq_zero_iff_dvd] at h_zero
      rw [← nat_cast_eq_zero_iff_dvd]
      exact h_zero
    exact Nat.coprime_not_dvd hcoprime.symm (Nat.Prime.ne_one hp) h_dvd
  apply (mul_right_inj' a_ne_zero).mp
  rw [mul_comm] at h
  ring_nf
  rw [add_comm]
  rw [Nat.cast_mul] at h
  rw [h]
  --goalの両辺にn+1をかけてhと一致させる

--aが正の整数で実際に示したい形式に変換
theorem katabami_theorem_fermat2 {n p : ℕ} (hp : p.Prime) (hn : n.Coprime p) (hn_pos : 0 < n) : n ^ (p - 1) ≡ 1 [MOD p] := by
  rw [← Nat.sub_add_cancel hn_pos]
  simp
  rw [Nat.sub_add_cancel hn_pos]
  have := fermat_via_binomial p (n - 1) hp (by rw [Nat.sub_add_cancel hn_pos]; exact hn)
  rw [← Nat.sub_add_cancel hn_pos] at this
  simp at this
  rw [Nat.sub_add_cancel hn_pos] at this
  exact this

--theorem3 剰余群
--theorem1で示した定理をここでも利用
theorem katabami_theorem_fermat3 (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]
  --pow_card_eq_oneはラグランジュの定理の帰結(Gの任意の元gに対して、gの位数はGの位数の約数なのでg^|G|=1)

#min_imports
