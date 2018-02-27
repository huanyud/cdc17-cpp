if [ -f main ]; then
    rm main
fi
g++ -I ~/lemon/include -L ~/lemon/lib -lemon -std=c++11 -o main main.cpp
./main
