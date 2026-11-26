import Kosa.Proof5

/-!
# 模組四的證明：前提體系的每一條定理

## 怎樣讀這個文件（給初次接觸 Lean 的讀者）

每條定理的格式是：

    theorem 名稱 (前提一) (前提二) … : 結論 := by
      證明步驟

* 括號裡的是**前提**。例如 `(a1 : «業假一» W)` 讀作「設業假一在世界 W 中成立，記作 a1」。
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
| `cases h : W.«繫不繫» c` | 「就 c 所繫之地，逐一分情況」     |
| `rw [h]`    | 「用 h 代入」                              |
| `absurd`    | 「兩者相違，此情況不可能」                  |
| `decide`    | 「兩個不同的值不相等，這可以直接判定」        |

符號：`∀` 凡，`∃` 有，`∧` 且，`∨` 或，`¬` 非，`→` 則，`↔` 即。
`W.«性» x = .«有覆無記»` 讀作「x 的性是有覆無記」。
-/

namespace Kosa.Lib

/-! ## 小引理：來自本體的適用條件 -/

/-- 表色必是色：身表唯在色處、語表唯在聲處（值的適用條件），有色自性者必是色。 -/
theorem «表色是色» (W : «世界») (O : «本體公理» W) (x : W.E)
    (h : «表色» W x) : W.«法類» x = .«色» := by
  have hZi : W.«色自性» x ≠ .«—» := by
    rcases h with h | h
    · rw [O.«適用_身表» x h]; decide
    · rw [O.«適用_語表» x h]; decide
  by_cases hx : W.«法類» x = .«色»
  · exact hx
  · exact absurd ((O.«適用_色自性» x).2 hx) hZi

/-- 癡不是見：見種只屬於慧，而癡的自性不是慧。 -/
theorem «癡無見種» (W : «世界») (O : «本體公理» W) (y : W.E)
    (h : W.«心所自性» y = .«癡») : W.«見種» y = .«—» :=
  (O.«適用_見種» y).2 (by rw [h]; decide)

/-- 五見是惑（定義）。 -/
theorem «五見是惑» (W : «世界») (x : W.E) (h : «五見» W x) : «惑» W x :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- 有伺、有漏的心，唯在欲界或初靜慮：
    有漏則非不繫（界約一）；有伺則非二定以上（界假六）。 -/
theorem «有伺有漏心唯欲界或初靜慮» (W : «世界») (k1 : «界約一» W) (a10 : «界假六» W)
    (c : W.E) (hXin : W.«法類» c = .«心») (hSi : W.«有伺無伺» c = .«有伺»)
    (hLou : W.«有漏無漏» c = .«有漏») :
    W.«繫不繫» c = .«欲界繫» ∨ W.«繫不繫» c = .«初靜慮繫» := by
  have hNotUpper : ¬ «二定以上» W c := by
    intro h2
    have h := a10 c ⟨h2, hXin⟩      -- 若在二定以上，則無伺
    rw [hSi] at h                    -- 但它有伺
    cases h                          -- 相違
  have hNotBuxi : W.«繫不繫» c ≠ .«不繫» := by
    intro h
    have h' := (k1 c).2 h            -- 若不繫，則無漏
    rw [hLou] at h'                  -- 但它有漏
    cases h'                         -- 相違
  cases hk : W.«繫不繫» c                -- 就 c 所繫之地分情況
  all_goals first
    | exact Or.inl rfl               -- 欲界：成立
    | exact Or.inr rfl               -- 初靜慮：成立
    | exact absurd hk hNotBuxi       -- 不繫：不可能
    | exact absurd (show «二定以上» W c by simp [«二定以上», «無色界繫», hk]) hNotUpper
                                     -- 二定以上：不可能

/-! ## 定理 -/

/-- 【業定一】色之善、染，唯由等起而成。依：業假一、業假二、業假三。 -/
theorem «業定一成立» (W : «世界») (O : «本體公理» W)
    (a1 : «業假一» W) (a2 : «業假二» W) (a3 : «業假三» W) : «業定一» W := by
  intro x ⟨hSe, hNotWufu⟩            -- 設 x 是色，且不是無覆無記
  cases h : W.«性由» x with           -- 它的善染由何而成？逐一看
  | «等起成» => rfl                   -- 等起成：正是要證的
  | «勝義成» =>                       -- 勝義成：色非勝義（業假一）
      exact absurd h (a1 x (Or.inr (Or.inr hSe)))
  | «自性成» =>                       -- 自性成：唯心所（業假二），而 x 是色
      have h2 := a2 x h
      rw [hSe] at h2
      cases h2
  | «相應成» =>                       -- 相應成：唯心心所（業假三），而 x 是色
      have h3 := a3 x h
      unfold «心心所» at h3
      rw [hSe] at h3
      rcases h3 with h' | h' <;> cases h'
  | «—» =>                            -- 無此門：只有無覆無記才無此門，而 x 不是
      exact absurd hNotWufu ((O.«適用_性由» x).1 h)

/-- 【業定二】善、染之色唯是業。依：業定一、業假四。 -/
theorem «業定二成立» (W : «世界») (d1 : «業定一» W) (a4 : «業假四» W) : «業定二» W := by
  intro x ⟨hSe, hNot⟩
  exact a4 x ⟨d1 x ⟨hSe, hNot⟩, hSe⟩   -- 等起所成之色是業

/-- 【業定三】有覆無記色唯是表色。依：業定二、業假五。 -/
theorem «業定三成立» (W : «世界») (d2 : «業定二» W) (a5 : «業假五» W) : «業定三» W := by
  intro x ⟨hXing, hSe⟩
  have hYe : «色業» W x := d2 x ⟨hSe, by rw [hXing]; decide⟩   -- 它是業：表或無表
  rcases hYe with h | h
  · exact h                                                -- 是表：成立
  · have hJi := a5 x h                                     -- 是無表：則有記（業假五）
    unfold «有記» at hJi
    rw [hXing] at hJi                                      -- 但它是有覆無記
    rcases hJi with h' | h' <;> cases h'                   -- 相違

/-- 【眠定一】五見唯見所斷。依：眠假二、眠假三。 -/
theorem «眠定一成立» (W : «世界»)
    (a16 : «眠假二» W) (a17 : «眠假三» W) : «眠定一» W := by
  intro x h5
  have hHuo := «五見是惑» W x h5               -- 五見是惑（定義）
  rcases a16 x hHuo with hJian | hXiu        -- 隨眠皆所斷：見所斷或修所斷
  · exact hJian
  · exact absurd (Or.inl h5) (a17 x ⟨hXiu, hHuo⟩)   -- 修所斷離見：相違

/-- 【眠定二】欲界有覆無記心唯見所斷。依：根假一、十三、十四、十五、眠定一、眠假四。 -/
theorem «眠定二成立» (W : «世界») (O : «本體公理» W)
    (a12 : «根假一» W) (a13 : «根定二» W) (a14 : «根假二» W) (a15 : «眠假一» W)
    (d4 : «眠定一» W) (a18 : «眠假四» W) : «眠定二» W := by
  intro c ⟨hYu, hXing, hXin⟩
  -- 染心必與癡相應（根假一）
  obtain ⟨y, hyChi, hcy⟩ := a12 c ⟨hXin, Or.inr hXing⟩
  -- 此癡與心同性、同地（根定二、十四）
  have hyXing : W.«性» y = .«有覆無記» := by rw [← a13 c y hcy]; exact hXing
  have hyYu : W.«繫不繫» y = .«欲界繫» := by rw [← a14 c y hcy]; exact hYu
  have hyHuo : «惑» W y := by unfold «惑»; simp [hyChi]   -- 癡是惑（定義）
  -- 欲界有覆無記隨眠，唯身見、邊見及彼俱癡（眠假一）
  rcases a15 y ⟨hyHuo, hyYu, hyXing⟩ with h | h | ⟨_, z, hyz, hz⟩
  · rw [«癡無見種» W O y hyChi] at h; cases h   -- 它是癡，不是身見
  · rw [«癡無見種» W O y hyChi] at h; cases h   -- 它是癡，不是邊見
  · -- 是與身見或邊見 z 相俱的癡
    have hzWu : «五見» W z := by
      rcases hz with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    have hzJian := d4 z hzWu                         -- z 見所斷（眠定一）
    have hyJian := a18 y z ⟨hyz, «五見是惑» W z hzWu, hzJian⟩   -- 故癡見所斷（眠假四）
    exact a18 c y ⟨hcy, hyHuo, hyJian⟩               -- 故心見所斷（眠假四）

/-- 【業定四】欲界無有覆無記表——頌「欲無有覆表，以無等起故」。
    依：定一、假六、假八、定五、假十九。 -/
theorem «業定四成立» (W : «世界») (O : «本體公理» W)
    (d1 : «業定一» W) (a6 : «業假六» W) (a8 : «業假八» W) (d5 : «眠定二» W) (a19 : «業假十一» W) :
    «業定四» W := by
  rintro ⟨r, hrYu, hrXing, hrBiao⟩     -- 設有欲界有覆無記表 r，往下推出矛盾
  have hrSe := «表色是色» W O r hrBiao
  have hrDeng := d1 r ⟨hrSe, by rw [hrXing]; decide⟩            -- r 由等起成（業定一）
  obtain ⟨c, hrc, hSame⟩ := a6 r ⟨hrSe, hrDeng⟩                 -- 有同性的剎那等起心 c（業假六）
  have hcXin := (O.«類型_剎那等起» r c hrc).2.1
  have hcXing : W.«性» c = .«有覆無記» := by rw [← hSame]; exact hrXing
  have hcYu : W.«繫不繫» c = .«欲界繫» := by rw [← a8 r c hrc]; exact hrYu   -- c 同在欲界（業假八）
  exact a19 r c hrc (d5 c ⟨hcYu, hcXing, hcXin⟩)   -- c 見所斷（眠定二），卻作剎那等起（違業假十一）

/-- 【業定五】表唯在欲界、初靜慮——頌「表唯有伺二」。
    依：假七、假九、假十、假八、假十一、約一。 -/
theorem «業定五成立» (W : «世界») (O : «本體公理» W)
    (a7 : «業假七» W) (a9 : «業假九» W) (a10 : «界假六» W) (a8 : «業假八» W)
    (a11 : «業假十» W) (k1 : «界約一» W) : «業定五» W := by
  intro r hrBiao
  obtain ⟨c, hrc⟩ := a7 r hrBiao                     -- 表必有剎那等起心（業假七）
  have hcXin := (O.«類型_剎那等起» r c hrc).2.1
  rw [a8 r c hrc]                                    -- 表與心同地（業假八）
  exact «有伺有漏心唯欲界或初靜慮» W k1 a10 c hcXin (a9 r c ⟨hrBiao, hrc⟩) (a11 r c hrc)

/-- 【業定六】有覆無記表唯在欲界、初靜慮。不需要業假七。
    依：定一、假六、假九、假十、假八、假十一、約一。 -/
theorem «業定六成立» (W : «世界») (O : «本體公理» W)
    (d1 : «業定一» W) (a6 : «業假六» W) (a9 : «業假九» W) (a10 : «界假六» W) (a8 : «業假八» W)
    (a11 : «業假十» W) (k1 : «界約一» W) : «業定六» W := by
  intro r ⟨hrXing, hrBiao⟩
  have hrSe := «表色是色» W O r hrBiao
  have hrDeng := d1 r ⟨hrSe, by rw [hrXing]; decide⟩
  obtain ⟨c, hrc, _⟩ := a6 r ⟨hrSe, hrDeng⟩         -- 剎那等起心由業假六給出，不必業假七
  have hcXin := (O.«類型_剎那等起» r c hrc).2.1
  rw [a8 r c hrc]
  exact «有伺有漏心唯欲界或初靜慮» W k1 a10 c hcXin (a9 r c ⟨hrBiao, hrc⟩) (a11 r c hrc)

/-- 【業定七】有覆無記表唯初靜慮繫。依：業定四、業定六。 -/
theorem «業定七成立» (W : «世界») (d6 : «業定四» W) (d7b : «業定六» W) : «業定七» W := by
  intro r ⟨hrXing, hrBiao⟩
  rcases d7b r ⟨hrXing, hrBiao⟩ with h | h
  · exact absurd ⟨r, h, hrXing, hrBiao⟩ d6        -- 在欲界：與業定四相違
  · exact h                                        -- 在初靜慮：成立

/-- 【業定八】有覆無記色唯初靜慮繫。依：業定三、業定七。 -/
theorem «業定八成立» (W : «世界») (d3 : «業定三» W) (d8 : «業定七» W) : «業定八» W := by
  intro r ⟨hrXing, hrSe⟩
  exact d8 r ⟨hrXing, d3 r ⟨hrXing, hrSe⟩⟩         -- 它是表（業定三），故唯初靜慮繫（業定七）

/-! ## 把整棵樹拼起來：從命題庫的假定、約定直接到業定八 -/

/-- 業定八由諸假定推出。前提是它在命題庫中的全部基礎（業假七不在其中）。
    「相應的心、心所同性」（根定二）不再是假定，而由 Proof5 中的「相應同性由諸假定」從相應五義與四種善推出。
    證明不再寫推理，只是把各條定理按「依」的關係拼接起來。 -/
theorem «業定八由諸假定» (W : «世界») (O : «本體公理» W) (k1 : «界約一» W) (kx : «根約一» W)
    (a1 : «業假一» W) (a2 : «業假二» W) (a3 : «業假三» W) (a4 : «業假四» W) (a5 : «業假五» W)
    (a6 : «業假六» W) (a8 : «業假八» W) (a9 : «業假九» W) (a10 : «界假六» W)
    (a11 : «業假十» W) (a12 : «根假一» W) (a14 : «根假二» W)
    (a15 : «眠假一» W) (a16 : «眠假二» W) (a17 : «眠假三» W) (a18 : «眠假四» W)
    (a19 : «業假十一» W) (b12 : «業假十二» W) (b13 : «業假十三» W) (b14 : «業假十四» W) :
    «業定八» W :=
  let r2 := «相應同性由諸假定» W O kx a1 b12 b13 b14
  let d1 := «業定一成立» W O a1 a2 a3
  let d2 := «業定二成立» W d1 a4
  let d3 := «業定三成立» W d2 a5
  let d4 := «眠定一成立» W a16 a17
  let d5 := «眠定二成立» W O a12 r2 a14 a15 d4 a18
  let d6 := «業定四成立» W O d1 a6 a8 d5 a19
  let d7b := «業定六成立» W O d1 a6 a9 a10 a8 a11 k1
  let d8 := «業定七成立» W d6 d7b
  «業定八成立» W d3 d8

end Kosa.Lib
