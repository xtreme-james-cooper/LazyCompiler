theory Type
imports Main
begin

datatype type = 
  Base
| Arrow type type
| Record "type list"
| Variant "type list"

end