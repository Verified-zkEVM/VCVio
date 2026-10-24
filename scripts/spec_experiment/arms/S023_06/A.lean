theorem forsNodeHashM_isTotalQueryBound (core : CorePrimitives p)
    (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) (l r : core.Y) :
    IsTotalQueryBound
      (forsNodeHashM core pk adrs z t l r : OracleComp (publicHashSpec core) core.Y) 1 :=
  PublicHash.h_isTotalQueryBound ..
