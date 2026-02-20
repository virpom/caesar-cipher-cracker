CXX      ?= c++
CXXFLAGS  = -std=c++17 -O2 -Wall -Wextra -Wno-unused-parameter
TARGET    = caesar

$(TARGET): caesar.cpp
	$(CXX) $(CXXFLAGS) -o $(TARGET) caesar.cpp

clean:
	rm -f $(TARGET)

.PHONY: clean
