cmake_minimum_required(VERSION 3.22)

project(evmint CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_FLAGS "-stdlib=libc++")

add_subdirectory(libs/range-v3/)
add_subdirectory(libs/magic_enum/)
add_subdirectory(libs/intx/)

add_executable(evmint main.cpp)
target_link_libraries(evmint PRIVATE range-v3 magic_enum intx::intx)
