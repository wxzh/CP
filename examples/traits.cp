--> "toggle to insert!"



{-

Simple traits

-}

--BEGIN_EDITOR
editor = trait => {
  on_key (key : String) = ();
  on_paint = ();
  save_file (name : String) = () };
--END_EDITOR

{-

Creating objects

-}


--BEGIN_EDITOR_INST
type Editor = { on_key : String -> Top, on_paint : Top, save_file : String -> Top };
my_editor1 = new editor;
--END_EDITOR_INST


{-

Trait inheritance & Abstract methods

-}

--BEGIN_VERSION
type Version = { version_num : Int };
--END _VERSION


--BEGIN_VERSION_EXT
editor2 = trait inherits editor => { version_num = 0.1 };
--END_VERSION_EXT


--BEGIN_RETRIEVE
type Retrieve = { get_version : Top -> Int };
retrieve = trait [self : Version] => { get_version (_ : Top) = self.version_num };
--END_RETRIEVE


--BEGIN_RETRIEVE_EXT
type EditorVersion = Editor & Version & Retrieve;
my_editor2 = new editor2 ,, retrieve;
--END_RETRIEVE_EXT


{-

Traits with parameters

-}

--BEGIN_MODAL
type ModalEdit =  { mode : String, toggle_mode : Top -> String };
--END_MODAL


--BEGIN_MODAL_DEF
modal_edit (init_mode : String) = trait [self : ModalEdit] => {
  mode = init_mode;
  version_num = 0.2;
  toggle_mode (_ : Top) =
    if self.mode == "command"
    then "toggle to insert!"
    else "toggle to command!" };
--END_MODAL_DEF


{-

Multiple inheritance and conflict resolving

--BEGIN_MODAL_CONFLICT
editor3 (init_mode : String) = trait [self : ModalEditor]
  -- conflicting field
  inherits editor2 ,, retrieve ,, modal_edit init_mode => { };
--END_MODAL_CONFLICT

-}

--BEGIN_MODAL_TYPE_DEF
type ModalEditor = EditorVersion & ModalEdit;
--END_MODAL_TYPE_DEF

--BEGIN_MODAL_OK
editor3 (init_mode : String) = -- trait [self : ModalEditor] inherits --advantage
  editor2 \ {version_num : Int} ,, retrieve ,, modal_edit init_mode;
--END_MODAL_OK

editor4 (init_mode : String) = trait [self : ModalEditor]
  inherits editor2 \ {version_num : Int} ,, retrieve ,,
           (modal_edit init_mode) \ {version_num : Int} => {
    version_num = 0.3
};


--BEGIN_MODAL_OK2
editor4 (init_mode : String) = trait [self : ModalEditor] inherits editor2 \ {version_num : Int} ,, retrieve ,, modal_edit init_mode  => {
    override version_num = 0.3
};
--END_MODAL_OK2


--BEGIN_MODAL_OK3
editor5 (init_mode : String) = trait [self : ModalEditor]
  inherits editor2 \ {version_num : Int} ,, retrieve ,, modal_edit init_mode => {
    override version_num = super.version_num + 0.1 };
--END_MODAL_OK3

--BEGIN_MODAL_OK4
editor6 (init_mode : String) = trait [self : ModalEditor]
  inherits editor2 \ {version_num : Int} ,, retrieve ,, modal_edit init_mode  => {
    override version_num = (editor2 ^ self).version_num + 0.1
};
--END_MODAL_OK4




-- {-

-- dynamic inheritance

-- -}


--BEGIN_MODAL_MIXIN
modal_mixin (A * ModalEditor)
            (editor : Trait[Top, Editor & A]) (init_mode : String) = 
    editor ,, retrieve ,, modal_edit init_mode;
--END_MODAL_MIXIN

--BEGIN_MODAL_USE
modal_editor = modal_mixin @Top editor "command";
my_editor3 = new modal_editor;
my_editor3.toggle_mode () -- Output: "toggle to insert!"
--END_MODAL_USE
