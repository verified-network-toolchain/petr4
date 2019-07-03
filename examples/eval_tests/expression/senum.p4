enum bit<2> Suits {
    Spade = 2w0,
    Diamond = 2w1,
    Heart = 2w2,
    Club = 2w3
}

const Suits a = Suits.Heart;

package EmptyPackage();
EmptyPackage() main;
