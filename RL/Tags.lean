import Lean

open Lean

initialize myTagAttr : TagAttribute ←
  registerTagAttribute `my_search_tag "mark theorems for search"
