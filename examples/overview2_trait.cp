--> "Process C-x on modal editor and Process C-x on spell editor for cutting text"

-------------------------- Mixin-style ----------------------------


-- BEGIN_OVERVIEW_EDITOR_TYPES
type Editor = {on_key : String -> String, do_cut : String, show_help : String};
type Version = {version : String};
-- END_OVERVIEW_EDITOR_TYPES

-- 1. Abstract method as self annotation
-- 2. Dynamic dispatch
-- BEGIN_OVERVIEW_EDITOR
editor = trait [self : Editor & Version] => {
  on_key(key : String) = "Pressing " ++ key;
  do_cut = self.on_key "C-x" ++ " for cutting text";
  show_help = "Version: " ++ self.version ++ " Basic usage..."
};
-- END_OVERVIEW_EDITOR

-- BEGIN_OVERVIEW_HELP
type Spelling = {check : String};
type OnKey = {on_key : String -> String};

spell_mixin (A * Spelling & OnKey)
            (base : Trait[Editor & Version, Editor & A])
  = trait [self : Editor & Version] inherits base => {
    override on_key(key : String) = "Process " ++ key ++ " on spell editor";
    check = super.on_key "C-c"  ++ " for spelling check"
  };
-- END_OVERVIEW_HELP


-- BEGIN_OVERVIEW_MODAL
type ModalEdit = {mode : String, toggle_mode : String};

modal_mixin (A * ModalEdit & OnKey)
            (base : Trait[Editor & Version, Editor & A])
= trait [self : Editor & Version] inherits base => {
    override on_key(key : String) = "Process " ++ key ++ " on modal editor";
    mode = "command";
    toggle_mode = "toggle succeeded"
  };
-- END_OVERVIEW_MODAL


-- BEGIN_OVERVIEW_LINE
type IDEEditor = Editor & Version & Spelling & ModalEdit;

ide_editor = trait [self : IDEEditor] inherits modal_mixin @Spelling (spell_mixin @Top editor) => {
  version = "0.2"
};
-- END_OVERVIEW_LINE


ide_editor = trait [self : IDEEditor] inherits spell_mixin @ModalEdit (modal_mixin @Top editor) => {
    version = "0.2"
};

--BEGIN_OVERVIEW_EDITOR_INST
a_editor1 = new ide_editor;
--END_OVERVIEW_EDITOR_INST

-------------------------- Trait-style ----------------------------


--BEGIN_HELP2
foo = trait => { version = "0.2" };
bar = new foo ,, editor;
--END_HELP2


-- BEGIN_FOO
foo (A * {bar : String}) (t : Trait[{bar : String} & A]) : Trait[A] = t;
-- END_FOO



--BEGIN_HELP
spell = trait [self : OnKey] => {
  on_key(key : String) = "Process " ++ key ++ " on spell editor";
  check = self.on_key "C-c"  ++ " for spell checking"
};
--END_HELP

--BEGIN_MODAL2
modal (init_mode : String) = trait => {
  on_key(key : String) = "Process " ++ key ++ " on modal editor";
  mode = init_mode;
  toggle_mode = "toggle succeeded"
};
--END_MODAL2


test = new modal "insert";


{-

--BEGIN_OVERVIEW_MODAL_CONFLICT
trait ide_editor (init_mode : String) [self : IDEEditor]
  -- conflict
  inherits editor ,, spell ,, modal init_mode {
    version = "0.2"
};
--END_OVERVIEW_MODAL_CONFLICT


-}

--BEGIN_OVERVIEW_MODAL_OK
ide_editor (init_mode : String) = trait [self : IDEEditor] 
  inherits editor \ {on_key : String -> String} ,,
           spell \ {on_key : String -> String} ,, modal init_mode => {
    version = "0.2"
};
--END_OVERVIEW_MODAL_OK


--BEGIN_OVERVIEW_MODAL_OK2
ide_editor2 (init_mode : String) = trait [self : IDEEditor]
  inherits editor \ {on_key : String -> String} ,,
           spell ,, (modal init_mode) \ {on_key : String -> String} => {
    version = "0.2"
};
--END_OVERVIEW_MODAL_OK2

--BEGIN_OVERVIEW_MODAL_OK3
ide_editor3 (init_mode : String) = trait [self : IDEEditor]
  inherits editor ,, spell \ {on_key : String -> String} ,,
           (modal init_mode) \ {on_key : String -> String} => {
    version = "0.2"
};
--END_OVERVIEW_MODAL_OK3


--BEGIN_OVERVIEW_MODAL_WIRE
ide_editor4 (init_mode : String) = trait [self : IDEEditor]
  inherits editor \ {on_key : String -> String} ,,
           spell \ {on_key : String -> String} ,,
           modal init_mode => {
    version = "0.2";
    override on_key(key : String) =
      super.on_key key ++ " and " ++ (spell ^ self).on_key key
};
--END_OVERVIEW_MODAL_WIRE

--BEGIN_OVERVIEW_MODAL_USE
a_editor2 = new ide_editor4 "command";
a_editor2.do_cut
-- "Process C-x on modal editor and Process C-x on spell editor for cutting text"
--END_OVERVIEW_MODAL_USE
