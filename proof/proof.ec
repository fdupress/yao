require Dkc.
require Gate.
require AdvGate.

(*TODOLIST :
  - Ecrire les jeux fake, real et hy
  - phi function
  - Spécifier les fonctions de gate
  - Ecrire les différents lemmes
*)

(*On introduit les jeux real, fake et Hy*)

(*On introduit l'adversaire*)

(*On montre que en fonction de l, on a une chance sur deux
de tomber sur les jeux(real, fake hy) correspondent*)

(*On montre la formule liant la probabilité de l'attaquant de
résussir avec celle de dkc*)

(*On doit être capable de montrer le lemme*)

(*lemma PrvInd : Gate.PrvInd.*)

(* ??? Composition demo *)

(*lemma PrvInd : Garble.PrvInd.*)





(*axiom temp : forall (ADVDKC<:Dkc.DKC_adv), forall &mDKC, forall (ADVGAR<:MainGame.GARBLE_adv), forall &mGAR,
     2%r * Pr[Dkc.Game(Dkc.DKC, ADVDKC).main()@ &mDKC:res] - 1%r
       =
     (2%r * Pr[MainGame.Game(MainGame.PrvInd, ADVGAR).main()@ &mGAR:res] - 1%r ) / 6%r.

lemma temp2 : forall (ADVDKC<:Dkc.DKC_adv), forall &mDKC, forall (ADVGAR<:MainGame.GARBLE_adv), forall &mGAR,
     Pr[MainGame.Game(MainGame.PrvInd, ADVGAR).main()@ &mGAR:res] <= Pr[Dkc.Game(Dkc.DKC, ADVDKC).main()@ &mDKC:res].

lemma PrvIndGarble : forall (ADV<:MainGame.GARBLE_adv), forall &m,
     Pr[MainGame.Game(MainGame.PrvInd, ADV).main()@ &m:res] <= epsilon.*)