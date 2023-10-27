package imports

import imported_files.{A => ClassA}

class ClassInSameFile

// Creates a QUALTHIS with a PackageRef inside
import ClassInSameFile as RenamedClassInSameFile

class RenamedImport
