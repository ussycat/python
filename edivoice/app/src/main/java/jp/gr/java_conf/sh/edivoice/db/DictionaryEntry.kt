package jp.gr.java_conf.sh.edivoice.db

import androidx.room.Entity
import androidx.room.PrimaryKey

@Entity(tableName = "dictionary")
data class DictionaryEntry(
    @PrimaryKey(autoGenerate = true) val id: Long = 0,
    val fromText: String,
    val toText: String
)
