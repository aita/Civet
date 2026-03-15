// swift-tools-version: 6.2
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription

let package = Package(
    name: "Civet",
    targets: [
        .target(name: "Syntax"),
        .target(
            name: "Parser",
            dependencies: ["Syntax"]
        ),
        .target(
            name: "Tree",
            dependencies: ["Syntax"]
        ),
        .target(
            name: "COIL",
            dependencies: ["Tree"]
        ),
        .target(
            name: "Machine",
            dependencies: ["COIL", "Tree"]
        ),
        .executableTarget(
            name: "Civet",
            dependencies: ["Parser", "Tree", "COIL", "Machine"]
        ),
        .testTarget(
            name: "CivetTests",
            dependencies: ["Parser", "Tree", "COIL", "Machine"]
        ),
    ]
)
