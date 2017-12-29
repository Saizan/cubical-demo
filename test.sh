agda --ignore-interfaces examples/Cubical/Examples/Cube.agda || exit 1
agda --ignore-interfaces examples/Cubical/Examples/Circle.agda || exit 1
rm -f examples/Cubical/Examples/Stream.agdai
agda examples/Cubical/Examples/Stream.agda || exit 1
rm -f src/Cubical/Sub.agdai
agda src/Cubical/Sub.agda || exit 1
agda src/Cubical/Everything.agda || exit 1
agda examples/Cubical/Examples/Everything.agda || exit 1
