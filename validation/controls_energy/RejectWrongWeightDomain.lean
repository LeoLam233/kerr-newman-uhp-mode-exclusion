import KN.Energy.Weights
-- x=-1 is negative but not in x<-(eta+2); actual P weights are negative here.
example : 0<KN.Energy.Pplus 0 (-1) :=
  (KN.Energy.weights_positive 0 (-1) (by norm_num) (by norm_num)).1
