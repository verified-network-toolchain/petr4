open AList

type 'tags_t t = { tags : 'tags_t; str : string }

type ('tags_t, 'v) coq_AList = ('tags_t t, 'v) AList.coq_AList
