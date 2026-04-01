module TheMasterForest

import Decidable.Equality
import Decidable.Equality.Core
import Data.Vect 

%default total 

data SKIExpr : Vect n Char -> Type where
    Var : Fin (length vs) -> SKIExpr vs
    S : SKIExpr vs
    K : SKIExpr vs
    I :SKIExpr vs
    (<*>) : SKIExpr vs -> SKIExpr vs ->SKIExpr vs

data SameExpr : SKIExpr vs -> SKIExpr vs -> Type where
    SameS : SameExpr (S <*> x <*> y <*> z) (x <*> z <*> (y <*> z))
    SameK : SameExpr (K <*> x <*> y) x
    SameI : SameExpr (I <*> x) x
    SameRefl : SameExpr x x
    SameTrans : SameExpr x y -> SameExpr y z -> SameExpr x z
    SameCong : SameExpr x y -> SameExpr z w -> SameExpr (x <*> z) (y <*> w)

alphaIntro : (v : _) -> SKIExpr vs -> SKIExpr (v :: vs)
alphaIntro v (Var x) = Var $ FS x
alphaIntro v S = S
alphaIntro v K = K
alphaIntro v I = I
alphaIntro v (x <*> y) = alphaIntro v x <*> alphaIntro v y

alphaEliminate : (e : SKIExpr (v :: vs)) -> (e' ** SameExpr (alphaIntro v e' <*> Var FZ) e)
alphaEliminate (Var FZ) = (I ** SameI) --principle 1
alphaEliminate (Var (FS x)) = (K <*> Var x ** SameK) --principle 2
alphaEliminate S = (K <*> S ** SameK) --principle 2
alphaEliminate K = (K <*> K ** SameK) --principle 2
alphaEliminate I = (K <*> I ** SameK) --principle 2
alphaEliminate x@(y <*> z) = 
    case project x of
        Nothing => 
            case project y of 
                Nothing => 
                    let (y' ** prf1) = alphaEliminate y
                        (z' ** prf2) = alphaEliminate z
                    in (S <*> y' <*> z' ** SameTrans SameS $ SameCong prf1 prf2) --principle 4
                (Just (y' ** prf)) => 
                    case z of
                        (Var FZ) => 
                            (y' ** SameCong prf SameRefl) --principle 3
                        _ => 
                            let (y' ** prf1) = alphaEliminate y
                                (z' ** prf2) = alphaEliminate z
                            in (S <*> y' <*> z' ** SameTrans SameS $ SameCong prf1 prf2) --principle 4
        (Just (x' ** prf)) => 
            (K <*> x' ** SameTrans SameK prf) --principle 2
where 
    project : (e : SKIExpr (v :: vs)) -> Maybe(e' ** SameExpr (alphaIntro v e') e)
    project (Var FZ) = Nothing
    project (Var (FS x)) = Just (Var x ** SameRefl)
    project S = Just (S ** SameRefl)
    project K = Just (K ** SameRefl)
    project I = Just (I ** SameRefl)
    project (x <*> y) =
        case project x of 
            Nothing => Nothing
            (Just (x' ** prf1)) => 
                case project y of 
                    Nothing => Nothing
                    (Just (y' ** prf2)) => 
                        Just (x' <*> y' ** SameCong prf1 prf2)

intro : (vs : _) -> SKIExpr [] -> SKIExpr vs
intro [] x = x
intro (v :: vs) x = (alphaIntro v $ intro vs x) <*> Var FZ

lemma1 : SameExpr e e' -> SameExpr (alphaIntro v e) (alphaIntro v e')
lemma1 SameS = SameS
lemma1 SameK = SameK
lemma1 SameI = SameI
lemma1 SameRefl = SameRefl
lemma1 (SameTrans x y) = SameTrans (lemma1 x) (lemma1 y)
lemma1 (SameCong x y) = SameCong (lemma1 x) (lemma1 y)

eliminate : {vs : _} -> (e : SKIExpr vs) -> (e' ** SameExpr (intro vs e') e)
eliminate {vs = []} e = (e ** SameRefl)
eliminate {vs = (v :: vs')} e = 
    let (e' ** prf1) = alphaEliminate e
        (e'' ** prf2) = eliminate e'
    in (e'' ** SameTrans (SameCong (lemma1 prf2) SameRefl) prf1)

expr : SKIExpr ['y', 'x']
expr = Var FZ <*> Var (FS FZ)
