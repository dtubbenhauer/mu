import WebMu.Revised.LocalPathSemantics
import WebMu.RevisedLocal

/-! The local proof, before collecting like terms. The complete elementary
histories, exponents and multiplicities are retained in each certificate. -/
namespace WebMu.Revised.LocalPaths
open Laurent Algebra Bar
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def word (s : String) : Word := s.toList.map fun c => c.toNat - 'A'.toNat

def route (u : String) (es : List (String × Int)) : Path :=
  es.foldl (fun p (w,d) => extend p ⟨word w,d,1⟩) (initial (word u))

def allPaths (n : Nat) (ss : List Step) : List Path :=
  (completeWords n).flatMap (downPaths ss)

def rSteps : List Step := [(.h,1),(.y,0)]
def lSteps : List Step := [(.h,0),(.y,1)]

theorem elementary_nonpositive :
    (allPaths 1 [(.y,0)]).all (fun p => p.degree ≤ 0) = true ∧
    (downPaths [(.cup,0)] []).all (fun p => p.degree ≤ 0) = true ∧
    (allPaths 2 rSteps).all (fun p => p.degree ≤ 0) = true ∧
    (allPaths 2 lSteps).all (fun p => p.degree ≤ 0) = true := by native_decide

theorem s_unique_positive :
    (allPaths 3 sSteps).filter (fun p => 0 < p.degree) =
      [route "ABC" [("ABBC",0),("ACAC",0),("ACAC",1)]] := by native_decide

theorem s_complete_ACAC :
    (allPaths 3 sSteps).filter (fun p => p.output == word "ACAC") =
      [route "ABC" [("ABBC",0),("ACAC",0),("ACAC",1)],
       route "ACB" [("ABCB",0),("ACBB",0),("ACAC",0)],
       route "BAC" [("ACAC",0),("ACAC",-1),("ACAC",1)]] := by native_decide


def middleRoute : Path := route "ACAC"
  [("ABCAC",0),("ABBBC",0),("ABBBBC",0),("ABBCAC",0),("ABCACAC",-1),("ABCACAC",1)]

theorem middle_nonpositive :
    (allPaths 4 middleSteps).all (fun p => p.degree ≤ 0) = true := by native_decide

theorem middle_unique_zero_ABC :
    (allPaths 4 middleSteps).filter (fun p => p.degree == 0 && p.output.take 3 == word "ABC") =
      [middleRoute] := by native_decide

def offenderRoute : Path := route "ABC"
  [("ABBC",0),("ACAC",0),("ACAC",1),
   ("ABCAC",0),("ABBBC",0),("ABBBBC",0),("ABBCAC",0),("ABCACAC",-1),("ABCACAC",1),
   ("ABBCACAC",0),("ACACACAC",0),("ACACACAC",1)]

theorem unique_excessive_path :
    (allPaths 3 innerSteps).filter (fun p => height (encode p.input) < p.degree) =
      [offenderRoute] := by native_decide

theorem offender_exact_data :
    offenderRoute.input = word "ABC" ∧ offenderRoute.output = word "ACACACAC" ∧
    offenderRoute.degree = 2 ∧ offenderRoute.multiplicity = 1 := by decide

/-- This is the actual five-step outer string, with all eight inputs retained. -/
theorem outer_path_bound :
    (allPaths 8 cSteps).all (fun p => p.degree + height (encode (p.output.take 3)) ≤ 0) = true := by
  native_decide

def ascWord : Word → Int
  | [a,b,c] => (if a<b then 1 else 0) + (if b<c then 1 else 0)
  | _ => 0

/-- The prefix and small-map order is the same as in each defining P_i h_i. -/
def summandPaths (s : List Step × List Step) (u : Word) : List Path :=
  downPaths (s.1 ++ s.2.reverse) u

theorem correction_ascent_paths :
    ((correctionSteps.take 7).flatMap fun s => (completeWords 3).flatMap (summandPaths s)).all
      (fun p => p.degree ≤ ascWord p.input) = true := by native_decide

theorem h_ascent_paths :
    (hSteps.flatMap fun s => (completeWords 3).flatMap (summandPaths s)).all
      (fun p => p.degree ≤ ascWord p.input) = true := by native_decide

theorem ascent_height : (completeWords 3).all (fun u => ascWord u ≤ 1+height (encode u)) = true := by
  native_decide

/-- The two exceptional prefixes, before attaching the identity small map. -/
theorem exceptional_prefix_paths :
    (allPaths 3 correctionSteps[0]!.1).all (fun p => p.degree ≤ if p.input == word "ABC" then 1 else 0) = true ∧
    (allPaths 3 hSteps[5]!.1).all (fun p => p.degree ≤ if p.input == word "ABC" then 1 else 0) = true := by
  native_decide

def aaaMiddleRoute : Path := route "AAAB"
  [("AABAB",0),("AAABB",0),("AAABAC",0),("AAAABC",0),("AAABABC",0),("AAAABBC",0)]

def aaaInnerRoute : Path := route "AAA"
  [("ABAA",0),("AABA",0),("AAAB",0),("AABAB",0),("AAABB",0),("AAABAC",0),
   ("AAAABC",0),("AAABABC",0),("AAAABBC",0),("ABAAABBC",0),("AABAABBC",0),("AAABABBC",0)]

def aaaOuterRoute : Path := route "AAABABBC"
  [("AABABABBC",0),("AAABBABBC",0),("AAABBABACC",0),("AAABBAACACC",0),("AAABBBAACACC",0)]

theorem aaa_middle_constant :
    (downPaths middleSteps (word "AAAB")).filter (fun p => p.degree == 0) = [aaaMiddleRoute] := by
  native_decide

theorem aaa_no_second_positive :
    ((downPaths middleSteps (word "AAAB")) ++ (downPaths middleSteps (word "BAAA"))).all
      (fun p => p.output.take 3 != word "ABC") = true := by native_decide

theorem aaa_inner_constant :
    (downPaths innerSteps (word "AAA")).filter (fun p => 0 ≤ p.degree) = [aaaInnerRoute] := by
  native_decide

theorem aaa_outer_constant :
    (downPaths cSteps (word "AAABABBC")).filter
      (fun p => 0 ≤ p.degree + height (encode (p.output.take 3))) = [aaaOuterRoute] := by
  native_decide

theorem aaa_outer_heights :
    (downPaths cSteps (word "AAABABBC")).all (fun p =>
      p.output.take 3 == word "AAA" || p.output.take 3 == word "AAB" ||
      p.output.take 3 == word "ABA" || p.output.take 3 == word "ABB") = true := by
  native_decide

def aaaBlockRoute : Path := route "AAA"
  [("ABAA",0),("AABA",0),("AAAB",0),("AABAB",0),("AAABB",0),("AAABAC",0),
   ("AAAABC",0),("AAABABC",0),("AAAABBC",0),("ABAAABBC",0),("AABAABBC",0),("AAABABBC",0),
   ("AABABABBC",0),("AAABBABBC",0),("AAABBABACC",0),("AAABBAACACC",0),("AAABBBAACACC",0)]

theorem aaa_block_constant :
    (downPaths blockSteps (word "AAA")).filter
      (fun p => 0 ≤ p.degree + height (encode (p.output.take 3))) = [aaaBlockRoute] := by
  native_decide

def prefixRoute : Path := route "AAA"
  [("ABAA",0),("AABA",0),("AAAB",0),("AAAAC",0),("ABAAAC",0)]

theorem prefix_path_bound :
    (allPaths 3 shortPrefixSteps).all
      (fun p => p.degree ≤ if p.input == word "ABC" then 1 else 0) = true := by native_decide

theorem prefix_path_height_bound :
    (allPaths 3 shortPrefixSteps).all (fun p => p.degree ≤ height (encode p.input)) = true := by native_decide

theorem prefix_unique_constant :
    (downPaths shortPrefixSteps (word "AAA")).filter (fun p => 0 ≤ p.degree) = [prefixRoute] := by
  native_decide

def tailZeroRoute : Path := route ""
  [("AC",0),("ABC",0),("AACC",0),("AABCC",0),("AABBCC",0),("AAACBCC",0),("AAABCBCC",0),("AAABBCBCC",0)]

/-- Ordered by the changed upward step, exactly as in the manuscript table. -/
def tailMinusOneRoutes : List Path := [
  route "" [("BB",-1),("ACB",0),("ABCB",0),("ABBCB",0),("AACBCB",0),("AABCBCB",0),("AABBCBCB",0),("AAACBCBCB",0)],
  route "" [("AC",0),("BAC",-1),("BABC",0),("BAACC",0),("BABACC",0),("BAACACC",0),("BAABCACC",0),("BAABBCACC",0)],
  route "" [("AC",0),("ABC",0),("ACAC",-1),("ACABC",0),("ABCABC",0),("ABBCABC",0),("ABBBCABC",0),("ABACBCABC",0)],
  route "" [("AC",0),("ABC",0),("AACC",0),("AACBC",-1),("AABCBC",0),("AAACCBC",0),("AAABCCBC",0),("AAABBCCBC",0)],
  route "" [("AC",0),("ABC",0),("AACC",0),("AABCC",0),("ABABCC",-1),("ABABBCC",0),("ABAACBCC",0),("ABABACBCC",0)],
  route "" [("AC",0),("ABC",0),("AACC",0),("AABCC",0),("AABBCC",0),("AACABCC",-1),("AACABBCC",0),("AABCABBCC",0)],
  route "" [("AC",0),("ABC",0),("AACC",0),("AABCC",0),("AABBCC",0),("AAACBCC",0),("AAACBBCC",-1),("AAABCBBCC",0)],
  route "" [("AC",0),("ABC",0),("AACC",0),("AABCC",0),("AABBCC",0),("AAACBCC",0),("AAABCBCC",0),("AABABCBCC",-1)]]

theorem tail_complete_top_paths :
    (downPaths tailSteps []).filter (fun p => -1 ≤ p.degree) =
      tailZeroRoute :: tailMinusOneRoutes.reverse := by native_decide

theorem tail_path_height_bound :
    (downPaths tailSteps []).all (fun p => p.degree + height (encode (p.output.take 3)) ≤ 0) = true := by
  native_decide

theorem tail_unique_shifted_constant :
    (downPaths tailSteps []).filter
      (fun p => 0 ≤ p.degree + height (encode (p.output.take 3))) = [tailZeroRoute] := by
  native_decide


theorem inner_excess_per_input : ∀ i : Fin 27,
    (downPaths innerSteps (triple i)).filter (fun p => height i < p.degree) =
      if i.val = 5 then [offenderRoute] else [] := by native_decide

/-- These checks split the ascent proof into the prefixes and their small maps. -/
def dInputLengths : List Nat := [3,3,2,2,2,2,2]
def hInputLengths : List Nat := [3,3,2,2,2,3,2,3,2,2,2]

theorem ordinary_d_prefix_nonpositive :
    (List.range 7).all (fun j => j == 0 ||
      (allPaths dInputLengths[j]! correctionSteps[j]!.1).all (fun p => p.degree ≤ 0)) = true := by
  native_decide

theorem ordinary_h_prefix_nonpositive :
    (List.range 11).all (fun j => j == 5 ||
      (allPaths hInputLengths[j]! hSteps[j]!.1).all (fun p => p.degree ≤ 0)) = true := by
  native_decide

theorem small_map_ascent_paths :
    (((correctionSteps.take 7) ++ hSteps).flatMap fun s =>
      allPaths 3 s.2.reverse).all (fun p => p.degree ≤ ascWord p.input) = true := by native_decide


theorem h_unique_positive_path :
    (allPaths 2 [(.h,0)]).filter (fun p => 0 < p.degree) =
      [route "AC" [("AC",1)]] := by native_decide

theorem s_AAA_complete_paths : downPaths sSteps (word "AAA") =
    [route "AAA" [("ABAA",0),("AABA",0),("AAAB",0)],
     route "AAA" [("BAAA",-1),("BAAA",0),("BAAA",0)]] := by native_decide

/-- Every individual elementary monomial has its stated positive multiplicity. -/
theorem elementary_multiplicity :
    ([Op.y,Op.h,Op.cup,Op.lam,Op.sigma].flatMap fun op =>
      allPaths (arity op) [(op,0)]).all (fun p => p.multiplicity == 1) = true := by native_decide

end WebMu.Revised.LocalPaths
