import Kosa.Lib

/-!
# 模組五的證明：阿羅漢最後心是苦諦、集諦；相應的心、心所同性

讀法與 Proof4.lean 相同：括號裡是前提，冒號後是結論，`by` 之後是證明步驟。
每條定理的前提，恰好是命題文件裡這條定理的「依」。本體約定（如苦諦、集諦的定義）
在 Lean 裡是展開即得的定義，不必另列。

`W.«阿羅漢最後心» x` 讀作「x 是阿羅漢最後心」。
-/

namespace Kosa.Lib

/-! ## 第一部分：阿羅漢最後心是苦諦、集諦 -/

/-- 【世間品6】最後心不是道諦。依：世間品2（二無記涅槃）、界品6（道諦唯善）。 -/
theorem «世間品6成立» (W : «世界») (a1 : «世間品2» W) (a6 : «界品6» W) : «世間品6» W := by
  intro x hx hDao
  have h := a6 x hDao          -- 若是道諦，則是善（界品6）
  rw [a1 x hx] at h            -- 但它是無覆無記（世間品2）
  cases h                      -- 相違

/-- 一個心若不是道諦，就是有漏：它是有為，而無漏的有為就是道諦。 -/
theorem «心非道諦則有漏» (W : «世界») (x : W.«法») (hXin : W.«法類» x = .«心»)
    (hNot : ¬ «道諦» W x) : W.«有漏無漏» x = .«有漏» := by
  cases h : W.«有漏無漏» x with
  | «有漏» => rfl
  | «無漏» =>
      exfalso
      apply hNot
      refine ⟨h, ?_⟩            -- 它是無漏；還要說明它是有為
      intro hWu                  -- 設它是無為
      rw [hXin] at hWu           -- 但它是心
      cases hWu

/-- 【世間品7】最後心是有漏。依：世間品6、世間品1（定義：最後心是心）。 -/
theorem «世間品7成立» (W : «世界») (d1 : «世間品6» W) (k2 : «世間品1» W) : «世間品7» W :=
  fun x hx => «心非道諦則有漏» W x ((k2 x).1 hx).1 (d1 x hx)

/-- 【界品13】苦諦、集諦範圍相等。由本體約定（二者都定義為有漏）直接得出。 -/
theorem «界品13成立» (W : «世界») : «界品13» W :=
  fun _ => Iff.rfl

/-- 【世間品8】阿羅漢最後心是苦諦、集諦。依：世間品7、界品13。 -/
theorem «世間品8成立» (W : «世界») (d2 : «世間品7» W) (d9 : «界品13» W) : «世間品8» W := by
  intro x hx
  have hKu : «苦諦» W x := d2 x hx          -- 有漏，即苦諦（本體約定）
  exact ⟨hKu, (d9 x).1 hKu⟩                 -- 苦諦、集諦範圍相等（界品13）

/-- 目標只依三條：最後心的定義（世間品1）、二無記涅槃（世間品2）、道諦唯善（界品6）。 -/
theorem «世間品8由諸假定» (W : «世界») (k2 : «世間品1» W) (a1 : «世間品2» W) (a6 : «界品6» W) :
    «世間品8» W :=
  «世間品8成立» W («世間品7成立» W («世間品6成立» W a1 a6) k2) («界品13成立» W)

/-- 也可以不用定義：頌「最後意識滅」已說最後心是意識，意識是心。 -/
theorem «世間品8_以意識代定義» (W : «世界») (O : «本體公理» W)
    (a1 : «世間品2» W) (a2 : «世間品3» W) (a6 : «界品6» W) : «世間品8» W := by
  intro x hx
  have hXin : W.«法類» x = .«心» := by
    by_cases h : W.«法類» x = .«心»
    · exact h
    · have := (O.«適用_六識» x).2 h                -- 不是心就沒有六識之分
      rw [a2 x hx] at this                         -- 但它是意識
      cases this
  have hLou := «心非道諦則有漏» W x hXin («世間品6成立» W a1 a6 x hx)
  exact ⟨hLou, hLou⟩

/-- 【界品14】染污法皆有漏。依：界品6、界品9、界品10。
    無漏的有為法是道諦，道諦是善；無漏的無為法，擇滅是善，非擇滅、虛空是無覆無記——都不是染。 -/
theorem «界品14成立» (W : «世界») (O : «本體公理» W)
    (a1 : «界品6» W) (a4 : «界品9» W) (a5 : «界品10» W) : «界品14» W := by
  intro x hRan
  cases h : W.«有漏無漏» x with
  | «有漏» => rfl
  | «無漏» =>
      exfalso
      have hNot : W.«性» x ≠ .«善» ∧ W.«性» x ≠ .«無覆無記» := by
        rcases hRan with h' | h' <;> (rw [h']; exact ⟨by decide, by decide⟩)
      by_cases hW : W.«法類» x = .«無為»
      · cases hk : W.«無為自性» x with                -- 三無為逐一看
        | «擇滅» => exact hNot.1 (a4 x hk)
        | «非擇滅» => exact hNot.2 (a5 x (Or.inl hk))
        | «虛空» => exact hNot.2 (a5 x (Or.inr hk))
        | «—» => exact ((O.«適用_無為自性» x).1 hk) hW
      · exact hNot.1 (a1 x ⟨h, hW⟩)                   -- 無漏的有為就是道諦

/-! ## 第二部分：相應的心、心所同性（原甲假九） -/

/-- 【根品14】相應可傳遞。依：根品1（相應五義）及本體（四種「同」可傳遞）。 -/
theorem «根品14成立» (W : «世界») (O : «本體公理» W) (k3 : «根品1» W) : «根品14» W := by
  intro x y z ⟨hxy, hyz, hne⟩
  obtain ⟨a1, a2, a3, a4⟩ := (k3 x y).1 hxy     -- x、y 同所依、同所緣、同行相、同時
  obtain ⟨b1, b2, b3, b4⟩ := (k3 y z).1 hyz     -- y、z 亦然
  exact (k3 x z).2 ⟨O.«傳遞_同所依» x y z a1 b1 hne, O.«傳遞_同所緣» x y z a2 b2 hne,
    O.«傳遞_同行相» x y z a3 b3 hne, O.«傳遞_同時» x y z a4 b4 hne⟩

/-- 引理：x 不是無覆無記時，與 x 相應的 y 與 x 同性。 -/
theorem «有記者之相應同性» (W : «世界») (O : «本體公理» W) (d7 : «根品14» W)
    (a10 : «業品3» W) (a11 : «業品7» W) (a12 : «業品8» W) (a13 : «業品9» W)
    (x y : W.«法») (hxy : W.«相應» x y) (hx : W.«性» x ≠ .«無覆無記») : W.«性» x = W.«性» y := by
  have hxXin := (O.«類型_相應» x y hxy).1        -- x 是心或心所
  have hyx := O.«對稱_相應» x y hxy
  cases hr : W.«性由» x with                     -- x 的善惡由何而成？
  | «勝義成» =>                                  -- 心、心所非勝義（業品3）
      exact absurd hr (a10 x (by rcases hxXin with h | h; exact Or.inl h; exact Or.inr (Or.inl h)))
  | «等起成» =>                                  -- 等起唯色、不相應行（業品7）
      exfalso
      rcases a11 x hr with h | h <;> (rcases hxXin with h' | h' <;> (rw [h'] at h; cases h))
  | «自性成» => exact (a13 y x ⟨hyx, hr⟩).symm      -- 與自性成者相應，同其性（業品9）
  | «相應成» =>                                  -- 有一個同性的自性成者 z 與 x 相應（業品8）
      obtain ⟨z, hxz, hz, hSame⟩ := a12 x ⟨hxXin, hr⟩
      rw [hSame]
      by_cases h : W.«性» z = W.«性» y
      · exact h
      · have hne : y ≠ z := fun e => h (by rw [e])  -- 若 y 就是 z，二者同性；既不同性，y 不是 z
        exact (a13 y z ⟨d7 y x z ⟨hyx, hxz, hne⟩, hz⟩).symm   -- y 亦與 z 相應（根品14），故同性
  | «—» => exact absurd hx ((O.«適用_性由» x).1 hr)  -- 只有無覆無記才無此門，而 x 不是

/-- 【根品15】相應的心、心所同性。依：根品14、業品3、業品7、業品8、業品9。 -/
theorem «根品15成立» (W : «世界») (O : «本體公理» W) (d7 : «根品14» W)
    (a10 : «業品3» W) (a11 : «業品7» W) (a12 : «業品8» W) (a13 : «業品9» W) :
    «根品15» W := by
  intro x y hxy
  by_cases hx : W.«性» x = .«無覆無記»
  · by_cases hy : W.«性» y = .«無覆無記»
    · rw [hx, hy]                                -- 兩者都是無覆無記
    · exact («有記者之相應同性» W O d7 a10 a11 a12 a13 y x (O.«對稱_相應» x y hxy) hy).symm
  · exact «有記者之相應同性» W O d7 a10 a11 a12 a13 x y hxy hx

/-- 把第二部分拼起來：相應法同性，由相應五義、本體與四條關於四種善的假定推出。 -/
theorem «相應同性由諸假定» (W : «世界») (O : «本體公理» W) (k3 : «根品1» W)
    (a10 : «業品3» W) (a11 : «業品7» W) (a12 : «業品8» W) (a13 : «業品9» W) :
    «根品15» W :=
  «根品15成立» W O («根品14成立» W O k3) a10 a11 a12 a13

/-! ## 順帶證明 -/

/-- 【世間品9】最後心是修所斷。依：世間品7、界品7、界品8、世間品2。 -/
theorem «世間品9成立» (W : «世界») (d2 : «世間品7» W) (a7 : «界品7» W) (a8 : «界品8» W)
    (a1 : «世間品2» W) : «世間品9» W := by
  intro x hx
  cases h : W.«斷非斷» x with
  | «修所斷» => rfl
  | «非所斷» =>                  -- 非所斷即無漏（界品7），但它有漏（世間品7）
      have hWu := (a7 x).1 h
      rw [d2 x hx] at hWu
      cases hWu
  | «見所斷» =>                  -- 不染非見所斷（界品8），而它無覆無記（世間品2），是不染
      exact absurd h (a8 x (Or.inl (Or.inr (a1 x hx))))

/-- 【世間品10】與最後心相應的心所，也是苦諦、集諦。依：世間品2、根品15、界品6。 -/
theorem «世間品10成立» (W : «世界») (O : «本體公理» W)
    (a1 : «世間品2» W) (d8 : «根品15» W) (a6 : «界品6» W) : «世間品10» W := by
  intro x y ⟨hx, hxy⟩
  have hyXing : W.«性» y = .«無覆無記» := by rw [← d8 x y hxy]; exact a1 x hx   -- 同性
  have hyXin := (O.«類型_相應» x y hxy).2.1                                   -- y 是心或心所
  have hLou : W.«有漏無漏» y = .«有漏» := by
    cases h : W.«有漏無漏» y with
    | «有漏» => rfl
    | «無漏» =>
        exfalso
        have hShan := a6 y ⟨h, by                 -- 若無漏，則是道諦（它是有為），故是善
          intro hWu
          rcases hyXin with h' | h' <;> (rw [h'] at hWu; cases hWu)⟩
        rw [hyXing] at hShan                       -- 但它無覆無記
        cases hShan
  exact ⟨hLou, hLou⟩

/-- 【世間品11】最後心是集諦，卻不是等無間緣。依：世間品7、根品4、世間品1。 -/
theorem «世間品11成立» (W : «世界») (d2 : «世間品7» W) (a5 : «根品4» W) (k2 : «世間品1» W) :
    «世間品11» W := by
  intro x hx
  obtain ⟨hXin, hA, hL⟩ := (k2 x).1 hx
  exact ⟨d2 x hx, a5 x ⟨Or.inl hXin, hA, hL⟩⟩

/-- 【世間品12】最後心的全貌。依：世間品2、世間品3、世間品4、世間品7、世間品9。 -/
theorem «世間品12成立» (W : «世界») (a1 : «世間品2» W) (a2 : «世間品3» W) (a3 : «世間品4» W)
    (d2 : «世間品7» W) (d3 : «世間品9» W) : «世間品12» W :=
  fun x hx => ⟨a2 x hx, a3 x hx, a1 x hx, d2 x hx, d3 x hx⟩

end Kosa.Lib
