module SingingBirds

import Data.DPair
import Decidable.Decidable
import Data.Fun
import Data.Rel
import ToMockAMockingbird
import BirdsGalore

%default total 

parameters {auto b : Type} {auto _ : Bird b} (xP : b) (Sings : b -> Type) {singsDec : Decidable 1 [b] Sings}
    0 Law1 : Type 
    Law1 = (x : b) -> (y : b) -> (Sings y) -> Sings $ xP <*> x <*> y 

    0 Law2 : Type 
    Law2 = (x : b) -> (y : b) -> Not(Sings x) -> Sings $ xP <*> x <*> y 

    0 Law3 : Type 
    Law3 = (x : b) -> (y : b) -> (Sings x) -> (Sings $ xP <*> x <*> y) -> Sings y

    0 Law4 : Type 
    Law4 = (x : b) -> Exists(\y => (Sings y -> Sings $ xP <*> y <*> x, (Sings $ xP <*> y <*> x) -> Sings y))

    lemma1 : Law1 -> Law2 -> (x : b) -> (y : b) -> (Sings x -> Sings y) -> Sings $ xP <*> x <*> y
    lemma1 law1 law2 x y prf = 
        case decision [b] Sings x of 
            (Yes prf2) => law1 x y $ prf prf2
            (No contra) => law2 x y contra

    0 question1 : Law1 -> Law2 -> Law3 -> Law4 -> (x : b) -> Sings x
    question1 law1 law2 law3 law4 x = 
        let Evidence y (prf1, prf2) = law4 x
            prf3 = \prf => law3 y x prf $ prf1 prf
            prf4 = lemma1 law1 law2 y x prf3
            prf5 = prf2 prf4
        in law3 y x prf5 prf4

    %ambiguity_depth 8
    0 question2 : Law1 -> Law2 -> Law3 -> {xL : b} -> Lark xL -> {xC : b} -> Cardinal xC -> (x : b) -> Sings x
    question2 law1 law2 law3 lark cardinal x = 
        question1 law1 law2 law3 law4 x
    where 
        law4 : (x : b) -> Exists(\y => (Sings y -> Sings $ xP <*> y <*> x, (Sings $ xP <*> y <*> x) -> Sings y))
        law4 x = 
            let eq1 = lark_lemma lark (xC <*> xP <*> x)
                (y**eq2) = the (y ** y = (ToMockAMockingbird.(<*>) (xL <*> ((xC <*> xP) <*> x)) (xL <*> ((xC <*> xP) <*> x)))) ((ToMockAMockingbird.(<*>) (xL <*> ((xC <*> xP) <*> x)) (xL <*> ((xC <*> xP) <*> x))) ** Refl)
                eq3 = trans eq1 (sym eq2)
                eq4 = cong (((xC <*> xP) <*> x) <*>) eq2
                eq5 = trans eq4 eq3
                eq6 = sym $ cardinal xP x y
                eq7 = trans eq6 eq5
            in Evidence (xC <*> xP <*> x <*> y) 
                (\prf => rewrite eq5 in rewrite eq7 in rewrite sym eq5 in prf,
                \prf => rewrite eq5 in rewrite sym eq7 in rewrite sym eq5 in prf)

    0 question3 : Law1 -> Law2 -> Law3 -> {a : b} -> ((x : b) -> (y : b) -> (z :b) -> a <*> x <*> y <*> z = x <*> (z <*> z) <*> y) -> (x : b) -> Sings x
    question3 law1 law2 law3 prf x = 
        question1 law1 law2 law3 law4 x
    where 
        law4 : (x : b) -> Exists(\y => (Sings y -> Sings $ xP <*> y <*> x, (Sings $ xP <*> y <*> x) -> Sings y))
        law4 x = 
            let eq1 = prf xP x ((a <*> xP) <*> x)
            in Evidence (a <*> xP <*> x <*> (a <*> xP <*> x)) 
                (\prf => rewrite sym eq1 in prf,
                \prf =>  rewrite eq1 in prf)
        