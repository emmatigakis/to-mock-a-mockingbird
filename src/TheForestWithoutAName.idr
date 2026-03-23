module TheForestWithoutAName

import Data.DPair
import Decidable.Decidable
import Data.Fun
import Data.Rel
import ToMockAMockingbird
import RusselsForest
import SingingBirds

parameters {auto b : Type} {auto _ : Bird b} (e : b) (Sings : b -> Type) 
    0 Law1 : Type 
    Law1 = (x : b) -> (y : b) -> (Sings $ e <*> x <*> y) -> Sings y

    0 Law2 : Type 
    Law2 = (x : b) -> (y : b) -> (Sings x) -> (Sings $ e <*> x <*> y) -> Void

    0 Law3 : Type 
    Law3 = (x : b) -> (y : b) -> Not(Sings x) -> (Sings y) -> Sings $ e <*> x <*> y

    0 Law4 : Type 
    Law4 = (x : b) -> Exists(\y => (Sings y -> Sings $ e <*> y <*> x, (Sings $ e <*> y <*> x) -> Sings y))

    Silent : b -> Type 
    Silent x = Not(Sings x)

    [SilentDec] Decidable 1 [b] Sings => Decidable 1 [b] Silent where
        decide x = 
            case decision [b] Sings x of 
                (Yes prf) => No $ \contra => contra prf
                (No contra) => Yes $ contra

    Law1' : Law1 -> Law2 -> Law3 -> Law4 -> SingingBirds.Law1 {b=b} e Silent
    Law1' law1 law2 law3 law4 x y prf1 prf2 = 
        prf1 $ law1 x y prf2
    
    Law2' : Law1 -> Law2 -> Law3 -> Law4 -> SingingBirds.Law2 {b=b} e Silent
    Law2' law1 law2 law3 law4 x y prf1 prf2 = 
        prf1 (\prf3 => law2 x y prf3 prf2)
    
    Law3' : Law1 -> Law2 -> Law3 -> Law4 -> SingingBirds.Law3 {b=b} e Silent
    Law3' law1 law2 law3 law4 x y prf1 prf2 prf3 = 
        prf2 $ law3 x y prf1 prf3

    Law4' : Law1 -> Law2 -> Law3 -> Law4 -> SingingBirds.Law4 {b=b} e Silent
    Law4' law1 law2 law3 law4 x = 
        let Evidence y (prf1, prf2) = law4 x
        in Evidence y (lemma1 prf1 prf2, lemma2 prf1 prf2)
    where 
        lemma1 : 
            (prf1 : Sings y -> Sings ((e <*> y) <*> x)) -> 
            (prf2 : Sings ((e <*> y) <*> x) -> Sings y) ->  
            (Sings y -> Void) -> 
            Sings ((e <*> y) <*> x) -> 
            Void 
        lemma1 prf1 prf2 prf3 prf4 = 
            prf3 $ prf2 prf4
        
        lemma2 : 
            (prf1 : Sings y -> Sings ((e <*> y) <*> x)) -> 
            (prf2 : Sings ((e <*> y) <*> x) -> Sings y) ->  
            (Sings ((e <*> y) <*> x) -> Void) -> 
            Sings y -> 
            Void
        lemma2 prf1 prf2 prf3 prf4 = 
            prf3 $ prf1 prf4

    0 question1 : Decidable 1 [b] Sings => Law1 -> Law2 -> Law3 -> Law4 -> (x : b) -> Silent x
    question1 law1 law2 law3 law4 x = 
        let law1' = Law1' law1 law2 law3 law4
            law2' = Law2' law1 law2 law3 law4
            law3' = Law3' law1 law2 law3 law4
            law4' = Law4' law1 law2 law3 law4
            silentDec = SilentDec
        in SingingBirds.question1 e Silent law1' law2' law3' law4' x
