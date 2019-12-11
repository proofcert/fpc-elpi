sig ljf-formulas.

kind form, i                    type. % Formulas and terms

type n, p           A -> form.         % Constructors of literals
type d-, d+      form -> form.         % Delays 
type &-&, &+&    form -> form -> form. % Conjunctions
type !+!         form -> form -> form. % Disjunction
type arr         form -> form -> form. % Implication
type all, some   (i -> form)  -> form. % Quantifiers
type f, t+, t-                   form. % Units

infixr &-&, &+&  6.
infixr !+!  5.
infixr arr 4.


% Note: there are no constructors for type atm.  In fact, I've removed
% atm for a polymorphic typing.  Ultimately, such polymorphism needs
% to be removed.

% The current strategy is to use atomic "client" formulas as atoms themselves.
