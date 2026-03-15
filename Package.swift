// swift-tools-version: 6.2
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription

let package = Package(
    name: "Civet",
    targets: [
        .target(
            name: "ChibiCC",
            cSettings: [
                .headerSearchPath("include"),
                .headerSearchPath("."),
                .define("_POSIX_C_SOURCE", to: "200809L"),
            ]
        ),
        .target(name: "Common"),
        .target(
            name: "Syntax",
            dependencies: ["Common"]
        ),
        .target(
            name: "Parser",
            dependencies: ["Common", "Syntax"]
        ),
        .target(
            name: "Tree",
            dependencies: ["Common", "Syntax"]
        ),
        .target(
            name: "COIL",
            dependencies: ["Common", "Tree"]
        ),
        .target(
            name: "Machine",
            dependencies: ["COIL", "Tree"]
        ),
        .target(
            name: "SyntaxMapper",
            dependencies: ["ChibiCC", "Syntax"]
        ),
        .executableTarget(
            name: "Civet",
            dependencies: ["Parser", "Tree", "COIL", "Machine"]
        ),
        .testTarget(
            name: "CivetTests",
            dependencies: ["Parser", "Tree", "COIL", "Machine"],
            resources: [.copy("Fixtures")]
        ),
    ]
)
