import Foundation

public struct SourceLocation: Sendable, Hashable {
    public let fileName: String
    public let line: Int
    public let column: Int

    public init(fileName: String, line: Int, column: Int) {
        self.fileName = fileName
        self.line = line
        self.column = column
    }
}
