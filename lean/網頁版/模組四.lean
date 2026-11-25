-- Kosa 模組四：前提體系（單文件版，可直接貼進 https://live.lean-lang.org 檢查）
-- 前半是由 Kosa 自動生成的本體與命題定義；後半是證明。

-- 本文件由 Kosa 自動生成（kosa/lean.py），請勿手改。
-- 模組：四・前提體系

namespace Kosa.M4

/-- 門：法類（心、心所、色） -/
inductive «法類值» where
  | «心» | «心所» | «色»
  deriving DecidableEq, Repr

/-- 門：心所類（惑、非惑心所） -/
inductive «心所類值» where
  | «惑» | «非惑心所» | «—»
  deriving DecidableEq, Repr

/-- 門：惑種（身見、邊見、邪見、見取、戒禁取、貪、瞋、癡、慢、疑） -/
inductive «惑種值» where
  | «身見» | «邊見» | «邪見» | «見取» | «戒禁取» | «貪» | «瞋» | «癡» | «慢» | «疑» | «—»
  deriving DecidableEq, Repr

/-- 門：色類（表色、無表色、非業色） -/
inductive «色類值» where
  | «表色» | «無表色» | «非業色» | «—»
  deriving DecidableEq, Repr

/-- 門：繫（欲界繫、初靜慮繫、第二靜慮繫、第三靜慮繫、第四靜慮繫、空無邊處繫、識無邊處繫、無所有處繫、非想非非想處繫、不繫） -/
inductive «繫值» where
  | «欲界繫» | «初靜慮繫» | «第二靜慮繫» | «第三靜慮繫» | «第四靜慮繫» | «空無邊處繫» | «識無邊處繫» | «無所有處繫» | «非想非非想處繫» | «不繫»
  deriving DecidableEq, Repr

/-- 門：性（善、不善、有覆無記、無覆無記） -/
inductive «性值» where
  | «善» | «不善» | «有覆無記» | «無覆無記»
  deriving DecidableEq, Repr

/-- 門：性由（勝義成、自性成、相應成、等起成） -/
inductive «性由值» where
  | «勝義成» | «自性成» | «相應成» | «等起成» | «—»
  deriving DecidableEq, Repr

/-- 門：斷（見所斷、修所斷、非所斷） -/
inductive «斷值» where
  | «見所斷» | «修所斷» | «非所斷»
  deriving DecidableEq, Repr

/-- 門：漏（有漏、無漏） -/
inductive «漏值» where
  | «有漏» | «無漏»
  deriving DecidableEq, Repr

/-- 門：伺（有伺、無伺） -/
inductive «伺值» where
  | «有伺» | «無伺» | «—»
  deriving DecidableEq, Repr

/-- 一個「世界」：論域 E，以及每個法在各門的取值、各關係。 -/
structure «世界» where
  E : Type
  «法類» : E → «法類值»
  «心所類» : E → «心所類值»
  «惑種» : E → «惑種值»
  «色類» : E → «色類值»
  «繫» : E → «繫值»
  «性» : E → «性值»
  «性由» : E → «性由值»
  «斷» : E → «斷值»
  «漏» : E → «漏值»
  «伺» : E → «伺值»
  «相應» : E → E → Prop
  «剎那等起» : E → E → Prop

/-- 定義：心心所＝心或心所 -/
def «心心所» (W : «世界») (x : W.E) : Prop := (W.«法類» x = .«心» ∨ W.«法類» x = .«心所»)

/-- 定義：染＝不善或有覆無記 -/
def «染» (W : «世界») (x : W.E) : Prop := (W.«性» x = .«不善» ∨ W.«性» x = .«有覆無記»)

/-- 定義：不染＝善或無覆無記 -/
def «不染» (W : «世界») (x : W.E) : Prop := (W.«性» x = .«善» ∨ W.«性» x = .«無覆無記»)

/-- 定義：有記＝善或不善 -/
def «有記» (W : «世界») (x : W.E) : Prop := (W.«性» x = .«善» ∨ W.«性» x = .«不善»)

/-- 定義：無記＝有覆無記或無覆無記 -/
def «無記» (W : «世界») (x : W.E) : Prop := (W.«性» x = .«有覆無記» ∨ W.«性» x = .«無覆無記»)

/-- 定義：所斷＝見所斷或修所斷 -/
def «所斷» (W : «世界») (x : W.E) : Prop := (W.«斷» x = .«見所斷» ∨ W.«斷» x = .«修所斷»)

/-- 定義：業＝表色或無表色 -/
def «業» (W : «世界») (x : W.E) : Prop := (W.«色類» x = .«表色» ∨ W.«色類» x = .«無表色»)

/-- 定義：五見＝身見或邊見或邪見或見取或戒禁取 -/
def «五見» (W : «世界») (x : W.E) : Prop := (W.«惑種» x = .«身見» ∨ W.«惑種» x = .«邊見» ∨ W.«惑種» x = .«邪見» ∨ W.«惑種» x = .«見取» ∨ W.«惑種» x = .«戒禁取»)

/-- 定義：色界繫＝初靜慮繫或第二靜慮繫或第三靜慮繫或第四靜慮繫 -/
def «色界繫» (W : «世界») (x : W.E) : Prop := (W.«繫» x = .«初靜慮繫» ∨ W.«繫» x = .«第二靜慮繫» ∨ W.«繫» x = .«第三靜慮繫» ∨ W.«繫» x = .«第四靜慮繫»)

/-- 定義：無色界繫＝空無邊處繫或識無邊處繫或無所有處繫或非想非非想處繫 -/
def «無色界繫» (W : «世界») (x : W.E) : Prop := (W.«繫» x = .«空無邊處繫» ∨ W.«繫» x = .«識無邊處繫» ∨ W.«繫» x = .«無所有處繫» ∨ W.«繫» x = .«非想非非想處繫»)

/-- 定義：二定以上＝第二靜慮繫或第三靜慮繫或第四靜慮繫或無色界繫 -/
def «二定以上» (W : «世界») (x : W.E) : Prop := (W.«繫» x = .«第二靜慮繫» ∨ W.«繫» x = .«第三靜慮繫» ∨ W.«繫» x = .«第四靜慮繫» ∨ «無色界繫» W x)

/-- 本體公理：適用條件、關係的類型約束、對稱。 -/
structure «本體公理» (W : «世界») : Prop where
  «適用_心所類» : ∀ x : W.E, W.«心所類» x = .«—» ↔ ¬(W.«法類» x = .«心所»)
  «適用_惑種» : ∀ x : W.E, W.«惑種» x = .«—» ↔ ¬(W.«心所類» x = .«惑»)
  «適用_色類» : ∀ x : W.E, W.«色類» x = .«—» ↔ ¬(W.«法類» x = .«色»)
  «適用_性由» : ∀ x : W.E, W.«性由» x = .«—» ↔ ¬(¬(W.«性» x = .«無覆無記»))
  «適用_伺» : ∀ x : W.E, W.«伺» x = .«—» ↔ ¬(W.«法類» x = .«心»)
  «類型_相應» : ∀ x y : W.E, W.«相應» x y → («心心所» W x) ∧ («心心所» W y) ∧ x ≠ y
  «對稱_相應» : ∀ x y : W.E, W.«相應» x y → W.«相應» y x
  «類型_剎那等起» : ∀ x y : W.E, W.«剎那等起» x y → (W.«法類» x = .«色») ∧ (W.«法類» y = .«心») ∧ x ≠ y

/-- 【約一】無漏 即 不繫 -/
def «約一» (W : «世界») : Prop :=
  (∀ x : W.E, (W.«漏» x = .«無漏» ↔ W.«繫» x = .«不繫»))

/-- 【假一】心或心所或色 非 勝義成 -/
def «假一» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«法類» x = .«心» ∨ W.«法類» x = .«心所» ∨ W.«法類» x = .«色») → ¬(W.«性由» x = .«勝義成»)))

/-- 【假二】自性成 唯 心所 -/
def «假二» (W : «世界») : Prop :=
  (∀ x : W.E, (W.«性由» x = .«自性成» → W.«法類» x = .«心所»))

/-- 【假三】相應成 唯 心心所 -/
def «假三» (W : «世界») : Prop :=
  (∀ x : W.E, (W.«性由» x = .«相應成» → «心心所» W x))

/-- 【假四】等起成・色 唯 業 -/
def «假四» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«性由» x = .«等起成» ∧ W.«法類» x = .«色») → «業» W x))

/-- 【假五】無表色 唯 有記 -/
def «假五» (W : «世界») : Prop :=
  (∀ x : W.E, (W.«色類» x = .«無表色» → «有記» W x))

/-- 【假六】凡 r：色(r) 且 等起成(r) ⇒ 有 c：剎那等起(r，c) 且 性(r)＝性(c) -/
def «假六» (W : «世界») : Prop :=
  (∀ r : W.E, ((W.«法類» r = .«色» ∧ W.«性由» r = .«等起成») → (∃ c : W.E, (W.«剎那等起» r c ∧ W.«性» r = W.«性» c))))

/-- 【假七】凡 r：表色(r) ⇒ 有 c：剎那等起(r，c) -/
def «假七» (W : «世界») : Prop :=
  (∀ r : W.E, (W.«色類» r = .«表色» → (∃ c : W.E, W.«剎那等起» r c)))

/-- 【假八】凡 r、c：剎那等起(r，c) ⇒ 繫(r)＝繫(c) -/
def «假八» (W : «世界») : Prop :=
  (∀ r c : W.E, (W.«剎那等起» r c → W.«繫» r = W.«繫» c))

/-- 【假九】凡 r、c：表色(r) 且 剎那等起(r，c) ⇒ 有伺(c) -/
def «假九» (W : «世界») : Prop :=
  (∀ r c : W.E, ((W.«色類» r = .«表色» ∧ W.«剎那等起» r c) → W.«伺» c = .«有伺»))

/-- 【假十】二定以上・心 唯 無伺 -/
def «假十» (W : «世界») : Prop :=
  (∀ x : W.E, ((«二定以上» W x ∧ W.«法類» x = .«心») → W.«伺» x = .«無伺»))

/-- 【假十一】凡 r、c：剎那等起(r，c) ⇒ 有漏(c) -/
def «假十一» (W : «世界») : Prop :=
  (∀ r c : W.E, (W.«剎那等起» r c → W.«漏» c = .«有漏»))

/-- 【假十二】凡 x：心(x) 且 染(x) ⇒ 有 y：癡(y) 且 相應(x，y) -/
def «假十二» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«法類» x = .«心» ∧ «染» W x) → (∃ y : W.E, (W.«惑種» y = .«癡» ∧ W.«相應» x y))))

/-- 【假十三】凡 x、y：相應(x，y) ⇒ 性(x)＝性(y) -/
def «假十三» (W : «世界») : Prop :=
  (∀ x y : W.E, (W.«相應» x y → W.«性» x = W.«性» y))

/-- 【假十四】凡 x、y：相應(x，y) ⇒ 繫(x)＝繫(y) -/
def «假十四» (W : «世界») : Prop :=
  (∀ x y : W.E, (W.«相應» x y → W.«繫» x = W.«繫» y))

/-- 【假十五】凡 y：惑(y) 且 欲界繫(y) 且 有覆無記(y) ⇒ 身見(y) 或 邊見(y) 或 （癡(y) 且 有 z：相應(y，z) 且 （身見(z) 或 邊見(z)）） -/
def «假十五» (W : «世界») : Prop :=
  (∀ y : W.E, ((W.«心所類» y = .«惑» ∧ W.«繫» y = .«欲界繫» ∧ W.«性» y = .«有覆無記») → (W.«惑種» y = .«身見» ∨ W.«惑種» y = .«邊見» ∨ (W.«惑種» y = .«癡» ∧ (∃ z : W.E, (W.«相應» y z ∧ (W.«惑種» z = .«身見» ∨ W.«惑種» z = .«邊見»)))))))

/-- 【假十六】惑 唯 所斷 -/
def «假十六» (W : «世界») : Prop :=
  (∀ x : W.E, (W.«心所類» x = .«惑» → «所斷» W x))

/-- 【假十七】修所斷・惑 非 五見或疑 -/
def «假十七» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«斷» x = .«修所斷» ∧ W.«心所類» x = .«惑») → ¬((«五見» W x ∨ W.«惑種» x = .«疑»))))

/-- 【假十八】凡 x、y：相應(x，y) 且 惑(y) 且 見所斷(y) ⇒ 見所斷(x) -/
def «假十八» (W : «世界») : Prop :=
  (∀ x y : W.E, ((W.«相應» x y ∧ W.«心所類» y = .«惑» ∧ W.«斷» y = .«見所斷») → W.«斷» x = .«見所斷»))

/-- 【假十九】凡 r、c：剎那等起(r，c) ⇒ 非 見所斷(c) -/
def «假十九» (W : «世界») : Prop :=
  (∀ r c : W.E, (W.«剎那等起» r c → ¬(W.«斷» c = .«見所斷»)))

/-- 【定一】色・非無覆無記 唯 等起成 -/
def «定一» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«法類» x = .«色» ∧ ¬(W.«性» x = .«無覆無記»)) → W.«性由» x = .«等起成»))

/-- 【定二】色・非無覆無記 唯 業 -/
def «定二» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«法類» x = .«色» ∧ ¬(W.«性» x = .«無覆無記»)) → «業» W x))

/-- 【定三】有覆無記・色 唯 表色 -/
def «定三» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«性» x = .«有覆無記» ∧ W.«法類» x = .«色») → W.«色類» x = .«表色»))

/-- 【定四】五見 唯 見所斷 -/
def «定四» (W : «世界») : Prop :=
  (∀ x : W.E, («五見» W x → W.«斷» x = .«見所斷»))

/-- 【定五】欲界繫・有覆無記・心 唯 見所斷 -/
def «定五» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«繫» x = .«欲界繫» ∧ W.«性» x = .«有覆無記» ∧ W.«法類» x = .«心») → W.«斷» x = .«見所斷»))

/-- 【定六】欲界繫・有覆無記・表色 無 -/
def «定六» (W : «世界») : Prop :=
  ¬((∃ x : W.E, (W.«繫» x = .«欲界繫» ∧ W.«性» x = .«有覆無記» ∧ W.«色類» x = .«表色»)))

/-- 【定七】表色 唯 欲界繫或初靜慮繫 -/
def «定七» (W : «世界») : Prop :=
  (∀ x : W.E, (W.«色類» x = .«表色» → (W.«繫» x = .«欲界繫» ∨ W.«繫» x = .«初靜慮繫»)))

/-- 【定七乙】有覆無記・表色 唯 欲界繫或初靜慮繫 -/
def «定七乙» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«性» x = .«有覆無記» ∧ W.«色類» x = .«表色») → (W.«繫» x = .«欲界繫» ∨ W.«繫» x = .«初靜慮繫»)))

/-- 【定八】有覆無記・表色 唯 初靜慮繫 -/
def «定八» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«性» x = .«有覆無記» ∧ W.«色類» x = .«表色») → W.«繫» x = .«初靜慮繫»))

/-- 【目標】有覆無記・色 唯 初靜慮繫 -/
def «目標» (W : «世界») : Prop :=
  (∀ x : W.E, ((W.«性» x = .«有覆無記» ∧ W.«法類» x = .«色») → W.«繫» x = .«初靜慮繫»))

end Kosa.M4


/-!
# 模組四的證明：前提體系的每一條定理

## 怎樣讀這個文件（給初次接觸 Lean 的讀者）

每條定理的格式是：

    theorem 名稱 (前提一) (前提二) … : 結論 := by
      證明步驟

* 括號裡的是**前提**。例如 `(a1 : «假一» W)` 讀作「設假一在世界 W 中成立，記作 a1」。
  每條定理的前提，恰好就是命題文件裡這條定理的「依」。
* 冒號後面是**結論**。
* `by` 之後是**證明步驟**。Lean 逐步檢查，每一步都必須由前面已有的東西嚴格推出；
  有一步不成立，整個文件就通不過。

證明步驟中常用的幾個詞：

| Lean        | 讀作                                     |
|-------------|------------------------------------------|
| `intro x h` | 「設 x 是任一法，且 h：x 滿足條件」          |
| `obtain ⟨c, h⟩ := …` | 「由……，有一個 c，使得 h」        |
| `have h : P := …` | 「得 P，記作 h」                    |
| `exact …`   | 「這正是要證的」                           |
| `cases h : W.«繫» c` | 「就 c 所繫之地，逐一分情況」     |
| `rw [h]`    | 「用 h 代入」                              |
| `absurd`    | 「兩者相違，此情況不可能」                  |
| `decide`    | 「兩個不同的值不相等，這可以直接判定」        |

符號：`∀` 凡，`∃` 有，`∧` 且，`∨` 或，`¬` 非，`→` 則，`↔` 即。
`W.«性» x = .«有覆無記»` 讀作「x 的性是有覆無記」。
-/

namespace Kosa.M4

/-! ## 兩條小引理：來自本體的適用條件 -/

/-- 有惑種（不是「—」）的法，必是惑。 -/
theorem «有惑種者是惑» (W : «世界») (O : «本體公理» W) (x : W.E)
    (h : W.«惑種» x ≠ .«—») : W.«心所類» x = .«惑» := by
  by_cases hx : W.«心所類» x = .«惑»
  · exact hx
  · exact absurd ((O.«適用_惑種» x).2 hx) h

/-- 有色類（不是「—」）的法，必是色。 -/
theorem «有色類者是色» (W : «世界») (O : «本體公理» W) (x : W.E)
    (h : W.«色類» x ≠ .«—») : W.«法類» x = .«色» := by
  by_cases hx : W.«法類» x = .«色»
  · exact hx
  · exact absurd ((O.«適用_色類» x).2 hx) h

/-- 有伺、有漏的心，唯在欲界或初靜慮：
    有漏則非不繫（約一）；有伺則非二定以上（假十）。 -/
theorem «有伺有漏心唯欲界或初靜慮» (W : «世界») (k1 : «約一» W) (a10 : «假十» W)
    (c : W.E) (hXin : W.«法類» c = .«心») (hSi : W.«伺» c = .«有伺»)
    (hLou : W.«漏» c = .«有漏») :
    W.«繫» c = .«欲界繫» ∨ W.«繫» c = .«初靜慮繫» := by
  have hNotUpper : ¬ «二定以上» W c := by
    intro h2
    have h := a10 c ⟨h2, hXin⟩      -- 若在二定以上，則無伺
    rw [hSi] at h                    -- 但它有伺
    cases h                          -- 相違
  have hNotBuxi : W.«繫» c ≠ .«不繫» := by
    intro h
    have h' := (k1 c).2 h            -- 若不繫，則無漏
    rw [hLou] at h'                  -- 但它有漏
    cases h'                         -- 相違
  cases hk : W.«繫» c                -- 就 c 所繫之地分情況
  all_goals first
    | exact Or.inl rfl               -- 欲界：成立
    | exact Or.inr rfl               -- 初靜慮：成立
    | exact absurd hk hNotBuxi       -- 不繫：不可能
    | exact absurd (show «二定以上» W c by simp [«二定以上», «無色界繫», hk]) hNotUpper
                                     -- 二定以上：不可能

/-! ## 定理 -/

/-- 【定一】色之善、染，唯由等起而成。依：假一、假二、假三。 -/
theorem «定一成立» (W : «世界») (O : «本體公理» W)
    (a1 : «假一» W) (a2 : «假二» W) (a3 : «假三» W) : «定一» W := by
  intro x ⟨hSe, hNotWufu⟩            -- 設 x 是色，且不是無覆無記
  cases h : W.«性由» x with           -- 它的善染由何而成？逐一看
  | «等起成» => rfl                   -- 等起成：正是要證的
  | «勝義成» =>                       -- 勝義成：色非勝義（假一）
      exact absurd h (a1 x (Or.inr (Or.inr hSe)))
  | «自性成» =>                       -- 自性成：唯心所（假二），而 x 是色
      have h2 := a2 x h
      rw [hSe] at h2
      cases h2
  | «相應成» =>                       -- 相應成：唯心心所（假三），而 x 是色
      have h3 := a3 x h
      unfold «心心所» at h3
      rw [hSe] at h3
      rcases h3 with h' | h' <;> cases h'
  | «—» =>                            -- 無此門：只有無覆無記才無此門，而 x 不是
      exact absurd hNotWufu ((O.«適用_性由» x).1 h)

/-- 【定二】善、染之色唯是業。依：定一、假四。 -/
theorem «定二成立» (W : «世界») (d1 : «定一» W) (a4 : «假四» W) : «定二» W := by
  intro x ⟨hSe, hNot⟩
  exact a4 x ⟨d1 x ⟨hSe, hNot⟩, hSe⟩   -- 等起所成之色是業

/-- 【定三】有覆無記色唯是表色。依：定二、假五。 -/
theorem «定三成立» (W : «世界») (d2 : «定二» W) (a5 : «假五» W) : «定三» W := by
  intro x ⟨hXing, hSe⟩
  have hYe : «業» W x := d2 x ⟨hSe, by rw [hXing]; decide⟩   -- 它是業：表或無表
  rcases hYe with h | h
  · exact h                                                -- 是表：成立
  · have hJi := a5 x h                                     -- 是無表：則有記（假五）
    unfold «有記» at hJi
    rw [hXing] at hJi                                      -- 但它是有覆無記
    rcases hJi with h' | h' <;> cases h'                   -- 相違

/-- 【定四】五見唯見所斷。依：假十六、假十七。 -/
theorem «定四成立» (W : «世界») (O : «本體公理» W)
    (a16 : «假十六» W) (a17 : «假十七» W) : «定四» W := by
  intro x h5
  have hHuo : W.«心所類» x = .«惑» := «有惑種者是惑» W O x (by
    intro hd; unfold «五見» at h5; rw [hd] at h5
    rcases h5 with h | h | h | h | h <;> cases h)
  rcases a16 x hHuo with hJian | hXiu        -- 隨眠皆所斷：見所斷或修所斷
  · exact hJian
  · exact absurd (Or.inl h5) (a17 x ⟨hXiu, hHuo⟩)   -- 修所斷離見：相違

/-- 【定五】欲界有覆無記心唯見所斷。依：假十二、十三、十四、十五、定四、假十八。 -/
theorem «定五成立» (W : «世界») (O : «本體公理» W)
    (a12 : «假十二» W) (a13 : «假十三» W) (a14 : «假十四» W) (a15 : «假十五» W)
    (d4 : «定四» W) (a18 : «假十八» W) : «定五» W := by
  intro c ⟨hYu, hXing, hXin⟩
  -- 染心必與癡相應（假十二）
  obtain ⟨y, hyChi, hcy⟩ := a12 c ⟨hXin, Or.inr hXing⟩
  -- 此癡與心同性、同地（假十三、十四）
  have hyXing : W.«性» y = .«有覆無記» := by rw [← a13 c y hcy]; exact hXing
  have hyYu : W.«繫» y = .«欲界繫» := by rw [← a14 c y hcy]; exact hYu
  have hyHuo : W.«心所類» y = .«惑» := «有惑種者是惑» W O y (by rw [hyChi]; decide)
  -- 欲界有覆無記隨眠，唯身見、邊見及彼俱癡（假十五）
  rcases a15 y ⟨hyHuo, hyYu, hyXing⟩ with h | h | ⟨_, z, hyz, hz⟩
  · rw [hyChi] at h; cases h          -- 它是癡，不是身見
  · rw [hyChi] at h; cases h          -- 它是癡，不是邊見
  · -- 是與身見或邊見 z 相俱的癡
    have hzWu : «五見» W z := by
      rcases hz with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    have hzJian := d4 z hzWu                         -- z 見所斷（定四）
    have hzHuo : W.«心所類» z = .«惑» :=
      «有惑種者是惑» W O z (by rcases hz with h' | h' <;> (rw [h']; decide))
    have hyJian := a18 y z ⟨hyz, hzHuo, hzJian⟩      -- 故癡見所斷（假十八）
    exact a18 c y ⟨hcy, hyHuo, hyJian⟩               -- 故心見所斷（假十八）

/-- 【定六】欲界無有覆無記表——頌「欲無有覆表，以無等起故」。
    依：定一、假六、假八、定五、假十九。 -/
theorem «定六成立» (W : «世界») (O : «本體公理» W)
    (d1 : «定一» W) (a6 : «假六» W) (a8 : «假八» W) (d5 : «定五» W) (a19 : «假十九» W) :
    «定六» W := by
  rintro ⟨r, hrYu, hrXing, hrBiao⟩     -- 設有欲界有覆無記表 r，往下推出矛盾
  have hrSe := «有色類者是色» W O r (by rw [hrBiao]; decide)
  have hrDeng := d1 r ⟨hrSe, by rw [hrXing]; decide⟩            -- r 由等起成（定一）
  obtain ⟨c, hrc, hSame⟩ := a6 r ⟨hrSe, hrDeng⟩                 -- 有同性的剎那等起心 c（假六）
  have hcXin := (O.«類型_剎那等起» r c hrc).2.1
  have hcXing : W.«性» c = .«有覆無記» := by rw [← hSame]; exact hrXing
  have hcYu : W.«繫» c = .«欲界繫» := by rw [← a8 r c hrc]; exact hrYu   -- c 同在欲界（假八）
  exact a19 r c hrc (d5 c ⟨hcYu, hcXing, hcXin⟩)   -- c 見所斷（定五），卻作剎那等起（違假十九）

/-- 【定七】表唯在欲界、初靜慮——頌「表唯有伺二」。
    依：假七、假九、假十、假八、假十一、約一。 -/
theorem «定七成立» (W : «世界») (O : «本體公理» W)
    (a7 : «假七» W) (a9 : «假九» W) (a10 : «假十» W) (a8 : «假八» W)
    (a11 : «假十一» W) (k1 : «約一» W) : «定七» W := by
  intro r hrBiao
  obtain ⟨c, hrc⟩ := a7 r hrBiao                     -- 表必有剎那等起心（假七）
  have hcXin := (O.«類型_剎那等起» r c hrc).2.1
  rw [a8 r c hrc]                                    -- 表與心同地（假八）
  exact «有伺有漏心唯欲界或初靜慮» W k1 a10 c hcXin (a9 r c ⟨hrBiao, hrc⟩) (a11 r c hrc)

/-- 【定七乙】有覆無記表唯在欲界、初靜慮。不需要假七。
    依：定一、假六、假九、假十、假八、假十一、約一。 -/
theorem «定七乙成立» (W : «世界») (O : «本體公理» W)
    (d1 : «定一» W) (a6 : «假六» W) (a9 : «假九» W) (a10 : «假十» W) (a8 : «假八» W)
    (a11 : «假十一» W) (k1 : «約一» W) : «定七乙» W := by
  intro r ⟨hrXing, hrBiao⟩
  have hrSe := «有色類者是色» W O r (by rw [hrBiao]; decide)
  have hrDeng := d1 r ⟨hrSe, by rw [hrXing]; decide⟩
  obtain ⟨c, hrc, _⟩ := a6 r ⟨hrSe, hrDeng⟩         -- 剎那等起心由假六給出，不必假七
  have hcXin := (O.«類型_剎那等起» r c hrc).2.1
  rw [a8 r c hrc]
  exact «有伺有漏心唯欲界或初靜慮» W k1 a10 c hcXin (a9 r c ⟨hrBiao, hrc⟩) (a11 r c hrc)

/-- 【定八】有覆無記表唯初靜慮繫。依：定六、定七乙。 -/
theorem «定八成立» (W : «世界») (d6 : «定六» W) (d7b : «定七乙» W) : «定八» W := by
  intro r ⟨hrXing, hrBiao⟩
  rcases d7b r ⟨hrXing, hrBiao⟩ with h | h
  · exact absurd ⟨r, h, hrXing, hrBiao⟩ d6        -- 在欲界：與定六相違
  · exact h                                        -- 在初靜慮：成立

/-- 【目標】有覆無記色唯初靜慮繫。依：定三、定八。 -/
theorem «目標成立» (W : «世界») (d3 : «定三» W) (d8 : «定八» W) : «目標» W := by
  intro r ⟨hrXing, hrSe⟩
  exact d8 r ⟨hrXing, d3 r ⟨hrXing, hrSe⟩⟩         -- 它是表（定三），故唯初靜慮繫（定八）

/-! ## 把整棵樹拼起來：從十九條假定、一條約定直接到目標 -/

/-- 目標由諸假定推出。前提恰是體系的全部基礎（假七不在其中）。
    證明不再寫推理，只是把上面各條定理按「依」的關係拼接起來。 -/
theorem «目標由諸假定» (W : «世界») (O : «本體公理» W) (k1 : «約一» W)
    (a1 : «假一» W) (a2 : «假二» W) (a3 : «假三» W) (a4 : «假四» W) (a5 : «假五» W)
    (a6 : «假六» W) (a8 : «假八» W) (a9 : «假九» W) (a10 : «假十» W)
    (a11 : «假十一» W) (a12 : «假十二» W) (a13 : «假十三» W) (a14 : «假十四» W)
    (a15 : «假十五» W) (a16 : «假十六» W) (a17 : «假十七» W) (a18 : «假十八» W)
    (a19 : «假十九» W) : «目標» W :=
  let d1 := «定一成立» W O a1 a2 a3
  let d2 := «定二成立» W d1 a4
  let d3 := «定三成立» W d2 a5
  let d4 := «定四成立» W O a16 a17
  let d5 := «定五成立» W O a12 a13 a14 a15 d4 a18
  let d6 := «定六成立» W O d1 a6 a8 d5 a19
  let d7b := «定七乙成立» W O d1 a6 a9 a10 a8 a11 k1
  let d8 := «定八成立» W d6 d7b
  «目標成立» W d3 d8

end Kosa.M4
