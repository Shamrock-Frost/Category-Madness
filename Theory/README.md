# Theory — law-based clients

`Category.lean` proves uniqueness of a left/right inverse from the public category
laws, then instantiates it against the sealed function category. It imports only
Interface vocabulary. The same source is checked against implementation and stub.

The compiled dependency audit follows transparent aliases and rejects private
implementation leaks. See `Prototype/MatrixCategory.md`.

Cites: D-CH-14, D-CH-25, D-RT-28, D-TL-17, AT-FD-2.
