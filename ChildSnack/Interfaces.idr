module ChildSnack.Interfaces

import ChildSnack.Token
import ChildSnack.Predicate
import ChildSnack.Domain

public export
Show Token where
  show (Bread i)        = "Bread \{show i}"
  show (Content i)      = "Content \{show i}"
  show (Sandwich i)     = "Sandwich \{show i}"
  show (Tray i)         = "Tray \{show i}"
  show (Place i)        = "Place \{show i}"
  show (Child i)        = "Child \{show i}"

public export
Show Predicate where
  show (Served c)       = "Served (\{show c})"
  show (OnTray(s, t))   = "OnTray (\{show s}, \{show t})"
  show (Waiting(c, p))  = "Waiting (\{show c}, \{show p})"
  show (At(t, p))       = "At (\{show t}, \{show p})"

public export
Show Mark where
    show mark = 
        "\n{" ++
        "\nplaces: " ++ 
        show mark.places ++ 
        "\nat_kitchen_bread: " ++ 
        show mark.at_kitchen_bread ++
        "\nat_kitchen_content:" ++ 
        show mark.at_kitchen_content ++
        "\nat_kitchen_sandwich:" ++ 
        show mark.at_kitchen_sandwich ++
        "\nno_gluten_bread:" ++ 
        show mark.no_gluten_bread ++
        "\nno_gluten_content:" ++ 
        show mark.no_gluten_content ++
        "\nontray:" ++ show mark.ontray ++
        "\nno_gluten_sandwich:" ++ 
        show mark.no_gluten_sandwich ++
        "\nallergic_gluten:" ++ 
        show mark.allergic_gluten ++
        "\nnot_allergic_gluten:" ++ 
        show mark.not_allergic_gluten ++
        "\nserved:" ++ 
        show mark.served ++
        "\nwaiting:" ++ 
        show mark.waiting ++
        "\nat:" ++ 
        show mark.at ++
        "\nnot_exist_sandwich:" ++ 
        show mark.not_exist_sandwich ++
        "\n}"
